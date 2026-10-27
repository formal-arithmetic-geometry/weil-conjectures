## Worker report

The module `Sheaf.AlgebraicGeometry.FppfFamilyCoproductDescentEncoding` states
`AlgebraicGeometry.fppf_family_coproduct_descent_encoding`, with its sole postponed proof
`sorry`. Its four helper definitions have real data: the double and triple comparison
cofans, the coproduct local scheme over the coproduct base, and the inclusion of a
represented component point. All are constructions belonging to the encoding in this
node, and are listed in `lean.declarations` with source and blueprint docstrings.

The live Q80 review is a stage-1 split review. There is no `lean` or `reviewed_lean`
record on the current node. Stage 2 therefore remains necessary; its work does not
resplit or modify the reviewed proof. No repair note exists for this item. The obsolete
CompactObject example module is now withdrawn, so its current empty module and the
standing brief's explicit header and record conventions were read together.

Clause-by-clause correspondence:

- The scheme T, set I, family T_i and maps f_i are `T : Scheme.{u}`,
  `I : Type (u + 1)`, `U : I → Scheme.{u}`, and `f : ∀ i, U i ⟶ T`.
  This is exactly the index/object universe interface of the recorded family datum.
- The fppf covering assumption is
  `hcov : Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T`.
  This includes flatness, local finite presentation and joint surjectivity.
- The fixed family scheme datum is `F : SchemeCoverDescentDatum f`.
  Its `localScheme`, `representation` and `data.hom` retain the supplied schemes
  and their actual transitions; no separate copy or stronger descent assumption is used.
- The coproducts the node tells us to form are the categorical chosen coproducts
  `∐ U` and `∐ fun i ↦ (F.localScheme i).left`. The two `HasCoproduct` arguments
  supply these constructions in the stipulated fixed universe. They impose neither
  finiteness, nonemptiness nor `Small.{u} I`: the statement works for any such
  coproducts that exist, including large-index families with mostly empty components.
  For the usual u-small families these arguments are already Mathlib instances.
  They do not select an alternative ambient universe or restrict the node's assumption
  that the displayed coproducts are formed in its fixed universes.
- The map A → T is `Sigma.desc f`. The map Z → A is
  `F.coproductScheme.hom`, defined by `CategoryTheory.Limits.Sigma.map` on the
  actual local structure maps. These are canonical constructions, not arbitrary maps.
- The three double-product identifications are the first three
  `Nonempty (IsColimit (schemeCoproductPairCofan ...))` conjuncts: AA, ZA and AZ.
  A colimiting cofan with vertex the displayed pullback means precisely that this
  pullback is the coproduct of the component pullbacks. The cofan legs are the
  actual `pullback.map` on coprojections, so the resulting isomorphisms preserve
  both projections. This is the universal-property formulation of the node's
  canonical identifications, not merely the existence of unrelated isomorphisms.
- The following four colimiting triple cofans give AAA, ZAA, AZA and AAZ. Their
  nested `pullback.map` legs retain all three coordinates and agree with the pair
  cofans. This includes the three local-scheme positions needed for the cocycle;
  no identification of complexes or derived objects occurs here.
- `∃ D : Over.DescentDatum (Sigma.desc f) F.coproductScheme` is the requested
  singleton datum on the specified v relative to the specified f. Its naturality,
  identity transport and triple cocycle are the fields of the recorded structure.
- The `∀ i, IsPullback ...` clause says that the inverse image of the i-th base
  coproduct component is exactly the original V_i, by its actual coprojection.
  Thus the local structure maps are also recovered.
- The following equality of `D.transport` on `F.coproductPoint i a x` with
  `(F.representation j).homEquiv.symm (F.data.hom ... x)` followed by the j-th
  coprojection is the prescribed component transition, on every test scheme,
  base point, pair of indices, overlap pair and represented local point. The
  equalities `ha`, `hb` express that the overlap pair has the same base point.
  Yoneda gives exactly the component isomorphism phi_ij. Along with the
  colimiting cofans this identifies global transport with coproduct phi_ij;
  applying it twice over a triple component identifies the singleton cocycle
  with the given family cocycle. Nothing asserts only abstract isomorphism of data.
- The singleton fpqc claim is
  `Presieve.singleton (Sigma.desc f) ∈ Scheme.fpqcPrecoverage T`.
  There is no `QuasiCompact (Sigma.desc f)` assumption or conclusion.
- The fixed-W claim is the `∀ W : Over T` biconditional. Its left side has a
  map q : Z → W and `IsPullback q v W.hom f`, together with invariance under
  every singleton transport. By the pullback universal property this is exactly
  an A-isomorphism W ×_T A ≅ Z identifying the canonical datum with D (inverting
  the pullback comparison if necessary). The right side has maps q_i : V_i → W,
  the Cartesian square for each f_i, and the exact component transition-invariance
  equation used in the recorded family effectivity definition. It is equivalently
  the compatible isomorphisms W ×_T T_i ≅ V_i. Both sides quantify the same W.
- The last conjunct `F.IsEffective ↔ D.IsEffective` uses both recorded predicates,
  without changing their definitions or replacing scheme effectivity by sheaf effectivity.
- No nonempty or finite index assumption appears. For I empty, hcov forces T empty;
  both coproducts and every W/T are empty and the affine-open fpqc test allows
  zero opens. Zero components and singleton coverings require no separate exception.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fpqcPrecoverage`; the former is the recorded family's actual covering condition.
- `Sheaf.AlgebraicGeometry.SchemeCoverDescentDatum`: `SchemeCoverDescentDatum`,
  its `data`, `localScheme`, `representation`, and `SchemeCoverDescentDatum.IsEffective`.
  The full structure and predicate were read, including the represented-test-point types.
- `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`:
  `CategoryTheory.Over.DescentDatum`, its `transport` and cocycle fields, and
  `CategoryTheory.Over.DescentDatum.IsEffective`. The full signatures and docstrings
  were read, including the Cartesian-square characterization of effectivity.
- `Mathlib.AlgebraicGeometry.Limits`: arbitrary small coproduct existence,
  `sigmaOpenCover`, and `disjoint_opensRange_sigmaι`. The universal-property interface
  is `Sigma.desc`, `Sigma.ι`, `Sigma.map`, `Cofan` and `IsColimit`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.map`, with scheme pullbacks supplied by Mathlib.
- `def-weil-size-convention` is the recorded metatheoretic convention, not a missing
  Lean declaration. Every universe and variable in the module is explicitly bound.

The proof plan is imported through these interfaces and the proof-only imports
`Mathlib.AlgebraicGeometry.Gluing`, `Mathlib.AlgebraicGeometry.PullbackCarrier`, and
`Sheaf.AlgebraicGeometry.FppfAffineRefinement`. The named refinement declaration is
`Scheme.exists_finite_fppf_affine_open_refinement`. The module docstring and theorem
docstring give the complete seven-step natural-language proof and its sources.

Edge cases checked: empty I and empty base; empty summands; a singleton cover;
an infinite family of copies of Spec k (its coproduct map need not be quasi-compact,
but it is an fpqc cover); arbitrary fixed W, including empty W; identity transitions;
and families that are not effective. In particular D is not constructed from a presumed
global W, and the statement does not assume effectivity of the family.

Searches made before writing:

- `msearch.py leanfinder`: “Fppf covering family descent data encoded by coproduct
  singleton descent datum preserving component transports and effectivity”. Eight hits,
  including `Pseudofunctor.isEquivalence_toDescentData`, `isStackFor_ofArrows_iff`,
  and `DescentData.isEquivalence_toDescentData_iff_of_sieve_eq`. They require a stack
  or equality of generated sieves and do not give this scheme encoding. The generic
  `DescentData` interface and its `hom`, cocycle and `iso` were also read directly.
- `msearch.py loogle`: `"DescentDatum", "coproduct"`. Zero hits.
- `msearch.py grep`: `descent.*(coprod|sigma)|coprod.*fpqc`, in AlgebraicGeometry.
  Zero hits.
- `rg` on both project roots for descent/coproduct, family/singleton and coproduct/fpqc
  combinations found related effectivity reductions and affine refinements, but no
  theorem with the encoding, component transports, product identifications and fixed-W
  equivalence. In particular `FppfFamilyAffineEffectivityReduction` uses this argument
  in its prose but only states effectivity under an affine-singleton hypothesis.
- The required node-id search in `lean/WeilConjectures` found no declaration.
  Exact-name searches for all five delivered declarations in both source roots also
  found none.

Sources checked locally: descent.tex, Definition 023V, family definition, and
Lemma 023X `lemma-family-is-one`, including its proof; topologies.tex,
`lemma-fppf-affine` (021P) and `definition-fpqc-covering` (022B).
No statement correction, dependency replacement, missing independent notion or
STATEMENT-DISPUTED fault was found.

Validation: `scompile.py Q109 lem-trf-fppf-family-coproduct-descent-encoding`
compiled the delivered file both as a sandbox and by its library module name, cleanly
(6.5 s and 6.4 s). The only postponed proof is the item theorem; all helper data are explicit.

## Second reading by Q109

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
