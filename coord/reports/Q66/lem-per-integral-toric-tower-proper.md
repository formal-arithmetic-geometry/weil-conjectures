## Worker report

Delivered statement: `AlgebraicGeometry.Monoscheme.integral_toric_tower_proper`
in `Sheaf.AlgebraicGeometry.IntegralToricTowerProper`. Its proof is `sorry`, as required
in stage 2. The construction module is
`Sheaf.AlgebraicGeometry.IntegralMonoschemeRealization`, owned by the new definition node
`def-per-integral-monoscheme-realization`. No existing notion is replaced. The original
item changes only in `lean` and by adding that new definition to `stmt_deps`.

Source read: local ILO PDF, Exposé VIII, printed pp.103--108, especially 3.2.2,
3.2.9, 3.2.17--3.2.18 and 3.3.3--3.3.5. Proposition 3.2.2 is explicitly over a general
base scheme, so the integer realization is part of the source construction, rather
than a field-only surrogate. The current `literature/blueprint/latest` ancestor
`lem-per-artin-gabber-affine-curve.md` and its proof were also read; they have no toric
statement of their own. This is the inherited ILO ingredient recorded in the item's
`blueprint.from`, consistent with its accepted split.

Clause matching:

- P fine and saturated: `(P : Type u) [CommMonoid P] (hfs : IsFineSaturatedMonoid P)`.
  The imported definition explicitly states finite generation, injectivity into the
  canonical group completion, and root saturation. Multiplicative notation is the
  same additive notion under `Multiplicative`; no restriction to sharp monoids.
- Its torsion-free completion G: `htf` quantifies over `Algebra.GrothendieckGroup P`
  and positive integers, requiring `g ^ m = 1` to imply `g = 1`.
- The finite saturated tower: `(n : ℕ) (T : Tower n)`. The recorded `Tower` retains
  every center and requires `IsSaturatedBlowup` for every step. That predicate includes
  `IsNonemptyCoherentIdeal`, as well as the canonical saturated charts and overlaps.
- M0 = Spec_mon P: `e : (T.level 0).space ≅ affine P`. This is identification with
  the actual unsharpened monoidal space, not with a fan or only a topological space.
- Z[Q]: actual `MonoidAlgebra ℤ Q`, whose finite-support basis multiplication is the
  required monomial multiplication. `integralDiagram` uses the existing
  `affineSections` diagram and the integer monoid-algebra functor; its open colimit is
  `integralRealization`. Localized restrictions are the diagram arrows, so gluing has
  the specified maps rather than arbitrary identifications.
- Arbitrary A and alpha: `(A : Type u) [CommRing A] (α : P →* A)`. No field,
  nonzero, reduced, flat, Noetherian or logarithmic condition is imposed on A.
  A shared universe loses no pair of objects, which can always be placed together
  in a larger universe. In particular no independently small test universe appears.
- Xi: `integralBaseChange A α (T.integralSpaceToBase e i)` is literally the scheme
  pullback of the two canonical maps to `Spec Z[P]`. The ring map from alpha is
  `(MonoidAlgebra.lift ℤ A P α).toRingHom`.
- Every transition proper: the first conjunct uses `IsProper (integralBaseMap ...
  (T.arrow j).map (T.integralSpaceToBase e j.castSucc))`. The source of this map is
  the pullback for `(T.arrow j).map ≫ T.integralSpaceToBase e j.castSucc`, exactly
  the successor-stage composite by the recursive definition of `integralSpaceToBase`.
  No unrelated transition map is an input.
- Composite pi proper: the second conjunct states properness of every stage's
  `integralBaseProjection`, in particular the last stage. This just includes all
  finite prefixes of the same asserted tower, including the identity prefix.
- Finite monoid-chart covers: `∀ i, ∃ r, ∃ C : Fin r → IntegralToricChart ...`.
  Its fields give Q ⊆ G, P ⊆ Q, fineness, saturation and
  `Subgroup.closure (Q : Set G) = ⊤`, the submonoid-in-G expression of Q^gp = G.
  Its `chart` is an actual affine monoid chart, and `overBase` fixes the base map.
  The first coverage assertion covers the actual monoscheme stage.
- Tensor-coordinate cover of Xi: the other two assertions give open immersions
  `(C j).baseChangeι A α` jointly covering Xi. Their domains are exactly
  `Spec (logIdealTensorRing A α (integralChartInclusion ...))`, namely
  `Spec (A ⊗[Z[P]] Z[Q])` with the two fixed scalar actions. The unique chart-map
  characterization specifies its first projection by `logIdealTensorBase` and
  second by `integralTensorRight` followed by the integer chart injection.
- Specified overlap maps: the next conjunct quantifies over any two toric charts
  C,D and any canonical incident monoid-chart map ψ,f, with
  `IsAffineMap ψ f` and equality of the two inclusions. It provides a tensor ring
  map l that fixes A and sends the Q-monomials by ψ, and the equality
  `C.baseChangeι ... = Spec.map l ≫ D.baseChangeι ...`. Applied to common localized
  refinements, these are precisely the prescribed overlap maps. Monomial and A
  generators determine the ring map, so the existential l is not arbitrary data.
- Localization refinement: for every fine Q and every submonoid S of Q, the next
  conjunct gives the explicit monomial l to the tensor ring of Q[S^-1], says
  `IsOpenImmersion (Spec.map l)`, and gives a ring equivalence E from localization
  at `integralTensorDenominators`. E agrees with l on the original ring and sends
  `integralTensorFraction ... a q s` to the monomial of `integralMonoidFraction Q S q s`,
  times a. The statement specifies the fraction formula in the node, including
  all ring relations; no domain embedding or cancellation in A is assumed.
- Torus locus S = alpha(P): `MonoidHom.mrange α` is exactly this submonoid, and
  `IsIso (pullback.snd (integralBaseProjection ...) (Spec.map (algebraMap A
  (Localization (MonoidHom.mrange α)))))` states that the actual base change of
  every stage's structural map is an isomorphism. This also makes all transition
  maps isomorphisms over that locus, by their projection equations.
- Fractions have denominators from S: the final conjunct quantifies over every
  `z : Localization (MonoidHom.mrange α)` and writes it as `Localization.mk a s`
  with `s : MonoidHom.mrange α`.

Recorded dependencies read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`, together with its public
  `LogRegularPair`: `AlgebraicGeometry.IsFineSaturatedMonoid`.
- `Sheaf.AlgebraicGeometry.MonoschemeToricRealization`:
  `Monoscheme.affine`, `Fine`, `Chart`, `AffineOpens`, `affineSections`, `AffineOpen`,
  `AffineOpen.inclusion`, `IsAffineMap`, `Tower`, `IsSaturatedBlowup`,
  `IsNonemptyCoherentIdeal`; read their full definitions and docstrings.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`; read their
  definitions and universal property. Scheme existence comes from Pullbacks.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
  Universally closed implies quasi-compact, so its locally-finite-type field has
  exactly the node's finite-type meaning.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, the quotient by
  bilinear relations. We use the already recorded tensor algebra rather than
  reconstructing it privately.
- `def-trf-log-ideal-chart-presentation`, module
  `Sheaf.AlgebraicGeometry.LogIdealChartPresentation`:
  `logIdealTensorRing`, `.commRing`, `logIdealTensorBase`, `logIdealTensorMonomial`.
  This existing definition node is cited from the new construction node.
- Proof-only imports include the recorded finite-saturation module; all recorded
  affine blowup chart, chart algebra, chart cover and properness modules; the
  recorded Proj standard-open module; and Mathlib ResidueField, Finite and Basic
  for the leaf tools. No import cycle was identified or omitted.

Construction obligations and data audit: the seven named postponed obligations are
`integralDiagram_gluing`, `existsUnique_integralMap`,
`existsUnique_integralToAffine`, `integralAffine_finiteCover`,
`integralAffine_isIso`, `existsUnique_integralBaseMap`,
`existsUnique_integralTensorChart`. Each belongs to the new definition node's
specified construction, is recorded in its `lean.declarations`, and has a source
and complete natural-language proof in its docstring. They postpone only gluing,
well-definedness, the canonical affine identification, and uniqueness properties.
The colimit uses Mathlib's actual gluing. Every chosen map is determined uniquely
by its statement. `integralAffine_finiteCover` supplies a proof-valued cover field,
not arbitrary object data. No definition has data supplied by sorry or by a bare
existence choice. All theorem proofs in this delivery are exactly `by sorry`.

Edge cases checked before and during statement drafting: n=0 leaves Fin n empty
and Fin(n+1) a singleton, so the composite is the initial affine identity. P may be
a group, or the zero additive monoid, without assuming sharpness. A=0 gives empty
spectra and permits empty base change. A with nilpotents or zero monomials is
allowed, and localization can be the zero ring. Centers with one generator and
the unit ideal give legitimate identity steps. Localization S={1} is the identity;
S=Q inverts the whole chart monoid. The tensor formulas do not suppose flatness
or injectivity of any coefficient map. No counterexample or statement dispute found.

Searches (all via the prescribed msearch.py wrapper):

- `leanfinder` query `Integral realization of a finite tower of saturated monoid blowups is proper after arbitrary base change, with tensor product affine charts and unchanged torus`: 8 hits, service succeeded. Returned names: AlgebraicGeometry.Proj.instIsProperToSpecZeroOfFiniteTypeSubtypeMemOfNatNat, AlgebraicGeometry.IsIntegralHom.instIsStableUnderBaseChangeScheme, AlgebraicGeometry.Proj.instUniversallyClosedToSpecZeroOfFiniteTypeSubtypeMemOfNatNat, AlgebraicGeometry.IsIntegralHom.instUniversallyClosed, AlgebraicGeometry.isIntegral_appTop_of_universallyClosed, AlgebraicGeometry.IsIntegralHom.instIsMultiplicativeScheme_1, AlgebraicGeometry.Scheme.Hom.instIsIntegralHomFromNormalization, AlgebraicGeometry.IsIntegralHom.instIsMultiplicativeScheme. No exact match.

- `loogle` query `AlgebraicGeometry.IsProper, AddMonoidAlgebra`: 0 hits, service succeeded. Returned names: . No exact match.

- `grep` query `toric|Monoscheme|monoscheme`: 0 hits, service succeeded. Returned names: . No exact match.

- `leansearch` query `Glue spectra of integer monoid algebras along localization maps to realize a monoscheme`: 8 hits, service succeeded. Returned names: AlgebraicGeometry.isIso_SpecMap_stakMap_localization, AlgebraicGeometry.Scheme.isOpenImmersion_SpecMap_localizationAway, AlgebraicGeometry.Spec_map_localization_isIso, PrimeSpectrum.localization_comap_isEmbedding, AlgebraicGeometry.AffineScheme, AlgebraicGeometry.IsPreimmersion.of_isLocalization, AlgebraicGeometry.isAffine_Spec, AlgebraicGeometry.structureSheafInType. No exact match.

- `leanfinder` query `Integral monoscheme realization gluing spectra Z[P]`: 8 hits, service succeeded. Returned names: AlgebraicGeometry.Spec, AlgebraicGeometry.instIsIntegralSpecOfIsDomainCarrier, AlgebraicGeometry.specZIsTerminal, AlgebraicGeometry.Scheme.GlueData.gluedScheme, AlgebraicGeometry.AffineSpace.toSpecMvPolyIntEquiv, AlgebraicGeometry.AffineSpace, AlgebraicGeometry.affine_isIntegral_iff, AlgebraicGeometry.Scheme.IdealSheafData.glueDataObjι. No exact match.

- `grep` query `integralRealization|integralDiagram|Monoscheme|toric`: 0 hits, service succeeded. Returned names: . No exact match.

Additional direct searches: `rg -n` in the project's `WeilConjectures` and `Sheaf`
for integral realization, monoid algebras over Z, toric towers and IntegralToricChart;
`grep -rn`/equivalent rg for the exact item id found no upstream declaration.
The existing `Monoscheme.realization` requires `[Field k]` in its full signature;
`CompleteToricFaceStrata` is a consumer mentioning this item in its proof docstring.
`rg -l 'integral toric|integral monoscheme' dag/nodes` found only the item.
`tools/blueprint_refs.py search 'integral toric'` returned zero blueprint nodes.
`dag/lean_names_upstream.json` supplies no duplicate integral realization notion.
The generic Scheme gluing and Spec hits are used as construction tools, and are
not statements of this result. Monoid localizations in an ambient group are written
as submonoid closure to retain the literal Q ⊆ G chart, rather than introducing
an unrelated quotient or changing the underlying monoid.

Validation: both delivered files compiled individually in dependency order through
`scompile.py`, in module mode, against the live published build. No errors or
non-sorry warnings. `deliver2.py --no-push` passed: commit abf2e15bfc4, preflight OK and both
files compiled. The first preflight metadata findings (required import_flags and
normalization of the recorded def keyword) were repaired before this passing run.

## New nodes

`def-per-integral-monoscheme-realization`: the actual integer monoid-algebra gluing,
canonical maps, affine identification, scheme pullback to A, prescribed tensor chart
maps and literal ambient-group localization/fraction notation. Source: ILO VIII
3.2.2 and 3.3.3--3.3.5, with affine monoid localization and chart notation from
3.1.4, 3.1.9, 3.1.21--3.1.22. Existing field-only realization does not provide Z[M].
This node reuses its Fine/Chart/affine-section definitions and the existing
LogIdealTensorRing. The logged LeanSearch, LeanFinder/Loogle and grep searches
above found no integral analogue. It is in the item's chapter and unit, cites the
existing definition nodes it builds on, and is cited by the item. Its theorem
obligations concern exactly the canonical construction stated in this definition.

## Second reading by Q66

Fresh clause-by-clause self-review, with node JSON, source and final Lean open;
the dispatch brief prohibits starting another agent, so the independent review
is the maintainer's review after this delivery, not a claimed second worker here.
The review found an initially missing explicit overlap clause; it was added as
the compatibility assertion for arbitrary incident toric charts, normalized on A
and on every monomial. All remaining clauses were matched above. A compiler error
from abbreviated `.ofHom` was repaired to the explicit `CommRingCat.ofHom`, and the
base-map definition was marked noncomputable because it uses the noncomputable
monoid spectrum. No mathematical statement correction was made. Re-read the
localization conclusion to verify it specifies the actual l and E fraction
formulas and the open immersion, and checked that the torus assertion is the
base change of the canonical projection rather than an arbitrary isomorphism.
