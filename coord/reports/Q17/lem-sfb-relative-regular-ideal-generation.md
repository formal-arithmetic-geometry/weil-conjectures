## Worker report

Stage 2 statement of `lem-sfb-relative-regular-ideal-generation`, in
`Sheaf.AlgebraicGeometry.RelativeRegularIdealGeneration`.
The existing Q118 pass concerns stage 1, not a Lean statement: the current node
has no Lean record and is a stage-2 queue item. The stage-handoff paragraph of
`coord/brief-stage2.md` explicitly permits this continuation. No accepted statement
or proof split is changed; only `lean` is added.

The module adds one real-data helper,
`AlgebraicGeometry.HilbertSectionBound.regularIdealMonomialMultiplier`, and the
theorem `AlgebraicGeometry.HilbertSectionBound.relative_regular_ideal_generation`,
whose entire proof is `sorry`. The helper pushes forward multiplication by the
actual integral-model monomial section, using the right unitor and the existing
basis-normalized twist pairing. It introduces no arbitrary map or chosen object.
The theorem's docstring contains the five-step proof from the accepted DAG.

Hypothesis and clause correspondence:

- `T Z : Scheme.{u}` are the base and closed scheme; `n : ℕ` includes zero.
  `ℙ(ULift.{u} (Fin (n + 1)); T)` is the existing base-change realization of
  projective n-space, with precisely n+1 homogeneous coordinates. `m : ℤ` and
  `hm : 1 ≤ m` impose precisely the stated regularity bound.
- `i` and `[IsClosedImmersion i]` are the specified closed immersion. The structural
  map is `projection T n`, the existing projective-space projection. The four
  instances `Flat`, `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated`
  on `i ≫ projection T n` give flatness and all three finite-presentation clauses.
- `i.ker.toModules` is the actual quasi-coherent ideal module associated to the
  closed immersion's kernel ideal, with its inclusion `i.ker.toModulesι`.
  `hfinite : Scheme.Modules.IsQuasiCoherentFiniteType i.ker.toModules` states both
  quasi-coherence and finite type, without imposing coherence on the whole base.
- The existing `idealTwist i b` is `i.ker.toModules ⊗ O(b)`, and
  `idealSections i b` is its ordinary pushforward K_b. Both are real constructions
  in `HilbertUniformSectionBound`, not new copies in this delivery.
- Each `(k : Type u) [Field k] [IsAlgClosed k] (g : Spec (.of k) ⟶ T)` is a geometric
  point. `ProjectiveSpace.map ... g` is the canonical projection from projective
  space over k to projective space over T. It is the ambient geometric fibre by
  the projective-space base-change square, `ProjectiveSpace.map_over`.
  The actual fibre immersion is `pullback.snd i (ProjectiveSpace.map ... g)`.
  Pullback pasting identifies its domain with `Z ×_T Spec k`.
- `hideal` says tensor pullback of the ideal is isomorphic to the kernel ideal of
  that fibre immersion. The displayed equality after composing with the ideal
  inclusion fixes the canonical comparison; a bare abstract isomorphism is not
  substituted. The structure-sheaf comparison is the existing
  `Scheme.Modules.tensorPullbackObjUnitToUnit`.
- `hcoherent` states Stacks 01BV coherence of each actual fibre ideal using the
  upstream `RingedSpace.IsCoherent`: finite type and finite-type kernels of maps
  from every finite free module on every open. This is the existing coherent
  clause of `pqf-def-coherent`. Its current primary Lean binding supplies the
  ambient quasi-coherent finite-type notion; the distinct coherent predicate is
  also already present upstream and is used, as in the regularity dependency.
- `hregular` quantifies over every such fibre and every `j : ℕ`, with `1 ≤ j` and
  `j ≤ n`. `Subsingleton ((RingedSpace.moduleCohomology ... j).obj (I_fibre ⊗ₘ
  O(m-j)))` is exactly the prescribed cohomology vanishing. This uses right derived
  global sections on module sheaves, not the separate abelian-sheaf Ext definition.
- `hfree` says `(idealSections i b).IsFiniteLocallyFree` for every integer b≥m.
  The existing finite-locally-free predicate allows locally varying finite rank;
  it does not assume a globally fixed rank or a global basis.
- `hbase` says the actual `Scheme.Modules.moduleBaseChangeMap` for the square
  `ProjectiveSpace.map_over ... g`, applied to `idealTwist i b`, is an isomorphism
  for every b≥m and geometric point. Its target is the direct image of the pulled
  back twisted ideal on projective space over k. `hideal`, the canonical twist
  base-change isomorphism, and pullback/tensor compatibility identify this with
  H⁰(I_fibre(b)); on Spec k this is the associated module of global sections.
  Composing with these fixed isomorphisms preserves and reflects `IsIso`, so no
  extra base-change hypothesis or different arbitrary comparison is imposed.
- `Epi (evaluation i m)` states surjectivity of the existing actual evaluation
  `p^*K_m ⊗ O(-m) → I`. Its definition is the section-normalized adjunction counit,
  followed by the twist pairing, O(0) identification and right unitor. `Epi` for
  module sheaves means local surjectivity (equivalently surjectivity on stalks),
  not surjectivity on sections over every open.
- The second conclusion ranges over `e : ℕ` and has target `K_(m+e)`. This is
  precisely the range of integer d≥m: e=(d-m).toNat gives d=m+e, and conversely
  each m+e≥m. This includes d=m with e=0.
- Its source is the existing literal homogeneous polynomial module
  `polynomialModule T n e = SheafOfModules.free ... (RelativeProjectiveSpace.monomials
  n e)` tensored with K_m. The monomial index is the existing degree-e exponent
  functions on Fin(n+1), not a chosen generating family.
- The conclusion supplies `μ`, asserts `Epi μ`, and fixes its restriction to EVERY
  monomial summand by the equality with `regularIdealMonomialMultiplier i m e a`.
  The coproduct/tensor universal property makes this exactly the polynomial
  multiplication map. Each component sends s to x^a s via the actual monomial
  section, so this is the map specified by the monomial identification
  `p_*O(e)=O_T[x_0,...,x_n]_e`, not existence of an unrelated epimorphism.

Dependency declarations used (source signatures and docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveSpace`, its
  projection, `ProjectiveSpace.map`, `ProjectiveSpace.map_over`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`: `ProjectiveSpace.twist`,
  `unitIsoTwistZero`, `pullbackMapTwistIso`; the twist is already defined over every
  base scheme by pullback from the integral model, so no new relative twist is needed.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistTensor`:
  `ProjectiveSpace.twistTensorIso`, normalized on standard-chart bases.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSectionAdjunction`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`; quasi-compactness and quasi-separatedness use the
  existing corresponding morphism classes.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`
  and `pullback.snd`, specialized to the geometric-point base-change square.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `Scheme.Modules.IsQuasiCoherentFiniteType`.
- `WeilConjectures.AlgebraicGeometry.Coherent`: `RingedSpace.IsCoherent`.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology` and
  `WeilConjectures.Topology.RingedSpaceModuleCohomology`:
  `sheafCohomologyAndHigherDirectImages`, `RingedSpace.moduleCohomology`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`:
  `Scheme.IdealSheafData.toModules`, `toModulesι`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFree`.
- `WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction`:
  `Scheme.Modules.moduleBaseChangeMap`.
- `Sheaf.AlgebraicGeometry.HilbertUniformSectionBound`:
  `projection`, `twist`, `idealTwist`, `idealSections`, `polynomialModule`,
  `monomialSection`, `idealTwistMultiplication`, `evaluation` in the
  `AlgebraicGeometry.HilbertSectionBound` namespace. These definitions already
  construct the exact objects needed here. The uniform-bound theorem is not used.
  This is an import of existing helper definitions from an ancestor's module,
  not a dependency on the ancestor's theorem or a new DAG edge. Since the ancestor
  has this item as a proof dependency, its future reverse proof-only import must
  be omitted under stage-2 rule 7 (it would close an import cycle). Moving these
  shared definitions into a common upstream module can be done in later maintenance.

All recorded proof-dependency modules are imported with plain imports when their
declarations are available, including the regularity theorem, pullback/tensor,
finite-type stalks, stalk exactness, pullback stalks, tensor right exactness,
faithfully flat field tensor detection, local Nakayama, stalkwise surjectivity,
and projective twist cohomology. None is reproved in stage 2.

Edge cases checked before drafting and on rereading:

- n=0 has one coordinate, not an empty index set; the regularity range 1≤j≤0 is
  empty as required, and multiplication still includes every power of x_0.
- m=1 is allowed, with arbitrary higher integers and arbitrary negative twists
  m-j in the hypothesis; m is not artificially restricted to nonnegative twists.
- d=m corresponds to e=0 and the unique constant monomial 1. The normalization
  gives scalar multiplication, not a missing positive-degree-only conclusion.
- T empty makes all geometric-point hypotheses vacuous and all module sheaves
  zero; no nonempty-base, rank-positivity, or nonzero-ring condition is imposed.
- Z=X has zero ideal and zero K_b; both maps are epic maps to zero. Z empty has
  unit ideal and the familiar monomial evaluation/multiplication maps.
- The geometric-field universe is the same u as the base, so residue fields and
  their algebraic closures are available. There is no independent smaller test
  universe that could make the fibre hypotheses vacuous.
- No Noetherian hypothesis on T, no reducedness, fixed fibre dimension or global
  rank is added. Only the fibre ideals are required to be coherent.

Searches (no exact existing theorem):

- `msearch.py`, LeanFinder: "Fibrewise Castelnuovo Mumford regularity gives relative
  generation of projective ideal and surjective section multiplication"; eight
  hits on Proj affine charts, localization and irrelevant ideals, none the relative
  regularity theorem.
- `msearch.py`, Loogle: "ProjectiveSpace, twist, multiplication"; no hits, unknown
  Mathlib identifier ProjectiveSpace. The project-specific definition was read
  directly in the upstream project source instead.
- `msearch.py`, grep:
  `relativeRegular|regularIdeal|projective.*[Tt]wist|relativeTwist|[Pp]rojective.*[Mm]ultiplication`;
  no Mathlib hits.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf`, including the item id and
  regularity/twist/multiplication terms: found the existing field regularity
  theorem, relative twists, and the Hilbert-uniform-bound module's exact helper
  constructions. Its theorem has a different uniform-bound statement and is not
  substituted for this node. The own declaration names have no existing hits.
- Read the complete relevant dependency signatures/docstrings and the current
  DAG records; read Stacks varieties.tex 08A6--08A8 and algebra.tex 00DV. The
  source's global-generation argument has an immaterial typo H⁰(F) for H⁰(F(m));
  the accepted node and this statement both use F(m).

Validation: the prescribed `scompile.py` compiled the module both as its sandbox
probe and under its library module name, within the default 60-second per-file
limit, with no errors or warnings. The only elaboration repairs were using the
existing scheme-module tensor notation and specifying the category of the
monomial coproduct whiskering. No statement correction or new node was needed.

No STATEMENT-DISPUTED fault remains. The old BLOCKED ending was a mistaken stage-1
handoff; it does not prohibit recording this stage-2 statement.

## Second reading by Q17

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
