## Worker report

The module `Sheaf.AlgebraicGeometry.ProperHenselianDerivedRestriction` states
`lem-per-proper-henselian-derived-restriction` in three theorem declarations, each with
`by sorry`. Its other three declarations are actual canonical constructions, with no
postponed data or proof. The node's mathematical statement, proof plan and source are
unchanged. Its statement dependencies gain the already landed
`def-weil-pbc-etale-sheaves` to name the existing abelian torsion-cohomology predicate.
No new nodes or dependency repairs are needed.

Hypothesis and clause correspondence:

- A commutative ring and ideal are `(A : Type u) [CommRing A] (I : Ideal A)`;
  the henselian-pair assumption is `[HenselianRing A I]`, the dependency's recorded
  Mathlib predicate, rather than a new copy of idempotent lifting.
- The affine base is `Spec (.of A)`, and the structural map is
  `f : Y ⟶ Spec (.of A)` with `[IsProper f]`. The only scheme-size choice is the
  project's `Scheme.{u}` convention; sheaf values use `AddCommGrpCat.{u + 1}`.
- The closed base immersion is exactly
  `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))`. Its fibre product with `f`
  is the node's Y0; `pullback.fst f (...)` is exactly i. No alternative closed
  subscheme or arbitrary comparison map is introduced.
- `K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})`
  says bounded below, with any integer lower bound and no upper bound.
  `hK : Y.HasTorsionEtaleCohomology K.obj` uses the existing predicate saying
  every integer cohomology sheaf is locally torsion. It does not impose a uniform
  annihilator on sections, stalks, or degrees.
- The restriction arrow is the dependency's
  `abelianDerivedCohomologyPullback i K`, with source and target the actual
  `Sheaf.Γ ... .rightDerivedFunctorPlus` objects. Exact inverse image is
  `(upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlus`.
  The main theorem states `IsIso` of this specific arrow, not existence of an
  unspecified isomorphism or only invertibility of its cohomology maps.
  These objects and arrows lie in D+(Ab), the full bounded-below subcategory of
  D(Ab). Full faithfulness of `DerivedCategory.Plus.ι` preserves and reflects
  invertibility and equality, so this is exactly the claimed statement in D(Ab).
  The right-derived functor API is computed by bounded-below injective resolutions;
  `KInjectiveBridge` is imported as the recorded resolution convention. The
  definition of the arrow is right-derived descent of ordinary section pullback.
- `proper_henselian_derived_restriction_naturality` quantifies over two bounded-below
  torsion complexes and every `a : K ⟶ L`. Its equation is
  `RΓ(a) ≫ rho_L = rho_K ≫ RΓ(i⁻¹a)`, giving naturality of these isomorphisms.
- The general clause, `proper_henselian_derived_restriction_pairs`, has independent
  commutative rings A and B, ideals I and J, both henselian hypotheses, and the
  ring map `φ : A →+* B` with exactly `hIJ : I ≤ J.comap φ`.
  It includes both proper structural morphisms f and g and any scheme map
  `h : V ⟶ Y` with `hh : h ≫ f = g ≫ Spec.map (CommRingCat.ofHom φ)`.
  There is no properness, cartesianity, flatness, or invertibility condition on h.
- `henselianClosedFibreMap I J φ hIJ f g h hh` is the induced h0. Its real
  construction is `pullback.map`, using the ring homomorphism
  `Ideal.quotientMap J φ hIJ`. The base-square proof is built directly from
  `Spec.map_comp` and `Ideal.quotientMap_comp_mk`, not postponed as a new theorem.
- L has the same bounded-below and torsion hypotheses over V as K over Y.
  The specified coefficient map is exactly
  `a : (upperStar ... h).mapDerivedCategoryPlus.obj K ⟶ L` and need not be an iso.
  `abelianDerivedSquareInverseImageIso` derives the canonical ordinary compositors
  `upperStarComp` and `mapDerivedCategoryPlusCompIso`. It identifies
  h0⁻¹ i⁻¹ K with j⁻¹ h⁻¹ K. `abelianDerivedSquareCoefficientMap` then follows
  this identification by j⁻¹a, so it is exactly a0, not an arbitrary chosen arrow.
  The square equation expands to
  `rho_Y ≫ T_h0(i⁻¹K) ≫ RΓ(a0) = T_h(K) ≫ RΓ(a) ≫ rho_V`.
  The equality `h0 ≫ i = j ≫ h` is supplied by the existing universal-property
  identity `pullback.lift_fst`, since `pullback.map` is the canonical lift.
  Applying the first theorem to g and L supplies the second restriction iso.
- No finite generation of I or J, Noetherianity, excellence, characteristic
  restriction, or invertibility of torsion primes occurs in any signature.

Dependency declarations used (full source signatures and docstrings read):

- `WeilConjectures.Mathlib.RingTheory.Henselian` publicly imports the Mathlib
  `HenselianRing` predicate; its `IsStrictlyHenselianLocalRing` declaration is
  also the dependency's recorded strict-local clause, which this item does not need.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, through
  `Mathlib.AlgebraicGeometry.Pullbacks`: `pullback`, `pullback.fst`, and
  `pullback.map`, with scheme fibre products supplied by the latter module.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the recorded derived
  category convention. Its `Etale.DerivedCategory.torsionCohomology` is the
  module-valued case; this abelian statement uses the recorded abelian specialization
  `AlgebraicGeometry.Scheme.HasTorsionEtaleCohomology` from
  `WeilConjectures.AlgebraicGeometry.EtaleSheaves` (the landed additional dependency).
  The latter is all integer homology sheaves being `CategoryTheory.Sheaf.IsTorsion`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact`:
  `AlgebraicGeometry.Etale.upperStar_abelian_exact`, with the existing exactness
  instances of `upperStar` used to form its exact derived functor.
- `WeilConjectures.CategoryTheory.KInjectiveBridge`:
  `CochainComplex.KInjectiveResolutionChoice`,
  `CategoryTheory.Functor.rightDerivedComplexWithResolution`, and the corresponding
  cohomology definition describe the node's chosen-resolution convention.
- `Sheaf.AlgebraicGeometry.ModuleDerivedCohomologyPullback`:
  `AlgebraicGeometry.Etale.abelianDerivedCohomologyPullback`, the already constructed
  canonical arrow, publicly importing the ordinary cohomology map and canonical Leray
  interface. Its own source explicitly constructs the right-derived descent of
  ordinary section pullback and compares resolutions.

All recorded proof-dependency modules are imported privately (except those already
public for the statement). Their declarations are the future proof plan: qcqs
higher-image torsion, truncation hypercohomology, the heart test, Gabber comparison,
proper base change, the derived exchange mate and adjunction, and unit--Leray pasting.
No proof is attempted in this delivery. All three postponed statements carry this
node's blueprint tag and the corresponding complete natural-language proof.

Edge cases checked before writing:

- I = 0: the quotient immersion is canonically an isomorphism; restriction is
  invertible. No nonzero or proper-ideal hypothesis was introduced.
- I = top: the Mathlib henselian-pair Jacobson condition forces A to be the zero
  ring; its spectrum and the proper scheme over it are empty. The statement
  retains this case, with no `[Nontrivial A]` assumption.
- Empty Y or V and the zero complex: all section objects/maps have their usual
  zero interpretation; nothing requires a geometric point or a nonempty fibre.
- Lower bounds may be negative and complexes may be unbounded above. The proof
  uses a finite filtration only in each fixed total degree, not global boundedness.
- Torsion includes residue-characteristic torsion and groups with no common
  annihilator; the local-section torsion predicate is essential here.
- Identity maps of pairs, I = J = 0, a = identity, and a = zero are included in
  the general square. The compositors are canonical even when inverse-image
  functors are only isomorphic, rather than definitionally equal.

Sources checked: `literature/stacks-project/etale-cohomology.tex`, labels
`theorem-gabber` (09ZI), `lemma-torsion-direct-image` (0DDD), and
`lemma-proper-base-change` (0DDE). These assert affine henselian comparison,
preservation of torsion cohomology under qcqs pushforward, and bounded-below
proper base change, respectively. The node assembles these exactly as its proof
plan states. No statement correction or disputed statement is needed.

Searches for an existing theorem and canonical objects:

- msearch leanfinder: "Proper scheme over henselian pair derived etale global
  sections bounded below torsion closed fibre restriction"; eight hits concerned
  formal-etale algebra and the etale site, not this derived comparison.
- msearch loogle: `HenselianRing, AlgebraicGeometry.IsProper`; zero hits.
- msearch grep in Mathlib/AlgebraicGeometry:
  `henselian.*cohomolog|cohomolog.*henselian|henselian.*proper`; zero hits.
- rg of the same expressions in project `lean/WeilConjectures` and `lean/Sheaf`
  found Gabber's affine sheaf-cohomology theorem, proper henselian degree-zero
  sections, and strict-henselian special cases, but no bounded-below proper
  derived restriction with both naturality clauses. The exact blueprint-id search
  in `lean/WeilConjectures` found no declaration for this item.
- Read `ModuleDerivedCohomologyPullback`, `CohomologyPullbackCanonicalArrows`,
  `Sites.DerivedSectionsUnitPasting`, `UpperLowerStar.Defs`, and `ExactFunctor`:
  these supply all canonical arrows and compositors needed. The helper definitions
  only specialize and compose those constructions for the fibre square; they do
  not introduce a competing inverse image, derived functor, or torsion predicate.

Validation: the complete file was checked with the prescribed server scompile.py;
syntax and elaboration errors were repaired. On 2026-10-24, deliver2.py --no-push
compiled both the sandbox and named library module without warnings and reported:
`OK (dry run): commit 8e79be3d3dd passes the preflight and compiles; nothing pushed`.
The delivery contains one Lean module, the item node, and this report.

## Second reading by Q122

The dispatcher prohibits starting other agents and assigns the independent delivery
review to the maintainer. No independent worker review is claimed here. A final
self-reading matched the file against every clause listed above, checked that the
coefficient compositor points from h0⁻¹i⁻¹K to j⁻¹h⁻¹K, and checked that the expanded
square composes with a0 on the correct side. The only corrections during elaboration
were Lean projection syntax and line wrapping; no mathematical statement changed.
