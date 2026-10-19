## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeProjectiveSpace` defines the relative-Proj
interface of projective r-space over an arbitrary scheme, not the base-change interface.
The original node statement and dependencies are unchanged. No new nodes or dependency
modules are needed. Every theorem proof is `sorry`; no definition contains `sorry`.

Clause-by-clause correspondence:

- The arbitrary scheme and nonnegative integer are namespace variables `(X : Scheme.{u})`
  and `(r : ℕ)`. No finiteness, separation, nonemptiness or base-field hypothesis is added.
- `freeModule X r` is `SheafOfModules.free` on `ULift (Fin (r + 1))`, hence precisely the
  coproduct of r+1 copies of the structure module. The lift only aligns universes.
  `SheafOfModules.ιFree (ULift.up i)` gives its ordered standard-basis inclusions.
- The underlying algebra is literally `SymmetricAlgebraSheaf.algebra (freeModule X r)`;
  `generator X r U i` applies its existing `inclusion` to the ith basis vector on U.
  This uses the constructed sheafification pair, not a pair chosen from mere existence.
- `monomials r n` consists of exponent tuples a with `∑ i, a i = n`.
  `monomial` evaluates `∏ i, generator ... i ^ a i`. `monomialUnit` is the linear map
  sending 1 to this monomial, and `monomialMap` extends these maps by the coproduct property.
- `IsSymmetricInput` fixes the actual underlying algebra sheaf, the nth homogeneous
  sheaf as the free sheaf on the degree-n monomials, and every homogeneous inclusion
  as `monomialMap`. Thus the nth homogeneous subsheaf is exactly the monomial span,
  with the inherited multiplication; there is exactly one degree-zero monomial, 1,
  so the zeroth piece and its inclusion are the structure module and algebra unit.
- `existsUnique_symmetricInput` is the named construction obligation. Its complete
  natural-language proof explains the universal-property comparison to the existing
  quasi-coherent pair, the standard-basis polynomial identification, and symmetric
  grading. Uniqueness is equality of the entire datum: the monomial inclusions fix
  the decomposition and, being monic, determine multiplication and unit. Other fields
  are proofs. Consequently `algebra` chooses uniquely determined data, not an unknown
  graded algebra. `algebra_eq` states the literal underlying-algebra equality.
- `coordinate` transports the existing generator across that equality into the section
  ring used by `RelativeProjAlgebra`. `coordinate_mem` places it in degree one.
- `existsUnique_affinePolynomialEquiv` specifies the canonical affine polynomial
  identification by its coefficient and variable equations. `affinePolynomialEquiv`
  selects only this unique equivalence. `affinePolynomial_homogeneous` states that
  the grading is polynomial total degree, including n=0.
- `construction X r` uses `exists_relativeProjData (algebra X r)`. That theorem specifies
  the realization up to the unique isomorphism commuting with its affine restrictions;
  this is a permitted universal-property construction. `scheme` and `π` are exactly
  `RelativeProjData.proj` and `.π`, with no different projective-space construction.
- The inherited `construction.restrictionIso V` identifies the inverse image of each
  affine V with Proj of the actual graded section ring. Its `restriction_over` and
  `restriction_compatibility` fields are the required base compatibility equations.
- `localStandardOpen V i` is exactly `Proj.basicOpen` at `coordinate V i`.
  `standardOpen i` is the union of its images over all affine bases. The theorem
  `standardOpen_restrict` identifies its restriction to each affine base with precisely
  that local open. Thus this union does not introduce a different chart interface.
- `localChart V i` is definitionally `Proj.basicOpenIsoSpec`, using `coordinate_mem`.
  Its target is `Spec (HomogeneousLocalization.Away ... (coordinate ...))`, the existing
  degree-zero homogeneous localization. Together with the polynomial equivalence it
  is the displayed polynomial localization in the node. No chart equivalence is chosen.
  The base restriction compatibility is inherited from relative Proj, whose local
  transition maps use precisely the coefficientwise homogeneous-localization maps.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms.
- `Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction`:
  `AlgebraicGeometry.SymmetricAlgebraSheaf.algebra` and `.inclusion` (full source read
  from the published upstream project; not present in this machine's side checkout).
- `Sheaf.LinearAlgebra.SymmetricAlgebra.Graded`:
  `SymmetricAlgebra.graded_by_tensor_images`, used in the construction proof plan.
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore`:
  `AlgebraicGeometry.exists_quasiCoherentSymmetricAlgebra_core`, universal property of
  that exact constructed pair (signature inspected on the compilation server).
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra`:
  `AlgebraicGeometry.exists_quasiCoherentSymmetricAlgebra`, providing the universal
  quasi-coherent pair and the generator-preserving affine-section equivalence.
- `Mathlib.LinearAlgebra.SymmetricAlgebra.Basis`:
  `SymmetricAlgebra.equivMvPolynomial`, `.equivMvPolynomial_ι_apply`, with any standard basis.
- `Sheaf.AlgebraicGeometry.RelativeProjData`:
  `AlgebraicGeometry.RelativeProjAlgebra`, `.sections`, `.sectionGrade`, `.localProj`,
  and `RelativeProjData`, `.proj`, `.π`, `.restrictionIso` and its compatibility fields.
- `Sheaf.AlgebraicGeometry.RelativeProjExists`:
  `AlgebraicGeometry.exists_relativeProjData`, retaining its universal characterization.
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`:
  `AlgebraicGeometry.Proj`, `.basicOpen`, `.basicOpenIsoSpec`.
- `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`:
  `HomogeneousLocalization.Away`, reused without a replacement localization.

Edge cases checked mathematically: r=0 has one homogeneous variable and one monomial
in every degree, so Proj is the expected relative projective zero-space; it is not
encoded with an empty set of coordinates. Degree zero has just the zero exponent
vector, hence is the structure sheaf. The empty base scheme, empty affine opens and
zero section rings are allowed; neither polynomial equivalences nor monomial free
module descriptions require a nontrivial ring. Arbitrary scheme universes are kept
by lifting the finite basis and monomial indexing types to u. No affine intersections
are assumed affine: standard opens are glued using all affine opens and refinements.

Searches (2026-10-15):

- `msearch.py ... leansearch "Relative projective space over a scheme using symmetric
  algebra with standard homogeneous localization charts"`: service unavailable,
  Internal Server Error; no verdict drawn from that search.
- `msearch.py ... leanfinder "Relative projective space is relative Proj of the symmetric
  algebra of a finite free sheaf"`: eight hits, including `AlgebraicGeometry.Proj`,
  `Proj.toSpecZero`, `Proj.fromOfGlobalSections`, `projIsoSpec`; absolute Proj only.
- `msearch.py ... loogle "AlgebraicGeometry.Proj, SheafOfModules.free"`: zero hits.
- `msearch.py ... grep "relativeProjective|RelativeProjective|symmetricAlgebraSheaf|SymmetricAlgebraSheaf"`:
  zero Mathlib hits.
- Local `rg` of those relative-projective and symmetric-algebra names in Mathlib,
  `WeilConjectures`, and `lean/Sheaf`: the upstream compactification file constructs
  the standard open immersion only for the base-change projective space. Reading
  `WeilConjectures/Compactification/ProjectiveSpace.lean` confirms that it explicitly
  uses the base change of the integral model; it is not this relative-Proj interface.
- `grep -rn "def-nagata-relative-projective-space" WeilConjectures`: no literal-id hits.
  The upstream name index has only `AffineSpace.toRelativeProjectiveSpace` and its
  open-immersion theorem, not any declaration in the new namespace.
- Targeted free-module and symmetric-algebra searches found `SheafOfModules.free`,
  `.ιFree`, and `SymmetricAlgebra.equivMvPolynomial`; these are reused.

The module compiles cleanly with `scompile.py` on the server, nice 19, two threads,
60 seconds per file. No local compiler or library build was run. No disputed statement
or source correction was needed. All named construction obligations and chart facts
are left as stage-2 theorem statements with complete proof plans in their docstrings.

## Second reading by ND

Independent reading, 2026-10-15. I read the node and its original blueprint source,
order 203, before matching the Lean. The source asks for symmetric-algebra relative
Proj and its homogeneous-localization charts over an arbitrary scheme; it adds no
Noetherian, separated, characteristic, or nonempty-base assumption. I also read the
Stacks source context in Modules, Section 01CF and Lemma 01CG (ringed spaces and
arbitrary modules), and Algebra, Section 00DM (finite free symmetric algebras).
The node copy has no statement_change and agrees with the repository statement.

Objects, hypotheses, and clauses, with their Lean renderings and verdicts:

1. An arbitrary scheme X and r in N: `variable (X : Scheme.{u}) (r : ℕ)`.
   Correct; no additional hypotheses or instances are required from the caller.
2. F = O_X^{r+1}, with ordered basis: `freeModule X r` is the existing
   `SheafOfModules.free` on `ULift (Fin (r + 1))`. I opened Mathlib's Free.lean:
   this is the coproduct of copies of `unit`, and `ιFree` is its inclusion.
   `generator` applies the existing symmetric-algebra inclusion to each basis
   vector evaluated at 1. Correct.
3. The actual constructed symmetric algebra and degree-one inclusion:
   `IsSymmetricInput` fixes `A.algebra.obj` to
   `SymmetricAlgebraSheaf.algebra (freeModule X r)`; `algebra_eq` exposes that
   equality, and `coordinate` transports `generator` along it. Correct.
   The construction and core files are absent in this machine's side checkout;
   I read both in the published server library at
   `/home/ubuntu/weil-conjectures-sheaf/lean/Sheaf/AlgebraicGeometry/`.
   `algebra` really sheafifies the sectionwise symmetric algebra under O_X;
   `inclusion` is the sheafification unit composed with the degree-one map.
   The core theorem quantifies over every algebra sheaf B and linear f, without
   assuming quasi-coherence of F. It is exactly the dependency needed here.
4. Symmetric-degree pieces and degree zero: `monomials r n` indexes precisely
   exponent vectors with sum n; `monomial` is the corresponding coordinate
   product. `monomialUnit` and `monomialMap` evaluate these monomials, with
   naturality postponed only in the named theorem `monomial_naturality`.
   `IsSymmetricInput` fixes every piece to the free monomial sheaf and every
   inclusion by HEq. `RelativeProjAlgebra.mul_eq` and `unit_eq` fix inherited
   multiplication and the structural unit. For n=0 the sole exponent vector
   is zero and its monomial is 1. Correct.
5. Quasi-coherence and the canonical affine polynomial identification:
   `RelativeProjAlgebra.algebra` has the existing `QuasiCoherentAlgebra` type.
   I read the quasi-coherent symmetric-algebra theorem: its universal pair and
   affine equivalence preserve scalars and degree-one generators; its only
   extra premise is quasi-coherence of the input, valid for this finite free F.
   `existsUnique_symmetricInput` describes the comparison with the actual
   constructed pair, and fixes the entire datum, not merely its existence.
   Fixing all monomial inclusions fixes the decomposition; their injectivity
   fixes multiplication and unit, and the other fields are proofs. Thus the
   chosen data is uniquely determined. Correct; no hollow definition.
   `existsUnique_affinePolynomialEquiv` fixes coefficients and every variable,
   so polynomial extensionality determines its chosen ring equivalence.
   `affinePolynomial_homogeneous` identifies every degree with the existing
   polynomial total-degree submodule. I opened Mathlib's Basis.lean and checked
   `equivMvPolynomial` and its generator equation. Correct.
6. The relative Proj scheme and structural morphism: `construction` selects
   from the recorded `exists_relativeProjData`; `scheme` is its `.proj` and
   `π` is its `.π`. I opened RelativeProjData.lean and RelativeProjExists.lean.
   Their input uses the actual graded section rings, and the existence theorem
   characterizes the result up to a unique chart-preserving isomorphism over X.
   This is a permitted universal-property construction. Correct.
7. Every affine base restriction and its compatibility: the retained datum's
   `restrictionIso V`, `restriction_over`, and `restriction_compatibility`
   specify the identifications over V and further restrictions. Its
   `localTransition` is `Proj.map` of the actual graded restriction map,
   with the existing homogeneous-localization chart maps. No intersection of
   affine opens is assumed affine. Correct.
8. Standard opens: `localStandardOpen V i` is exactly `Proj.basicOpen` at the
   actual coordinate; `standardOpen i` glues these by their images in the
   scheme; `standardOpen_restrict` gives precisely the prescribed restriction
   on each affine base. Correct, with no independently chosen open.
9. Chart identification: `localChart V i` is literally the existing
   `Proj.basicOpenIsoSpec`, with positivity `Nat.one_pos` and degree-one
   membership `coordinate_mem`. Its target uses `HomogeneousLocalization.Away`
   on the actual graded section ring, identified with the displayed polynomial
   graded ring by `affinePolynomialEquiv` and `affinePolynomial_homogeneous`.
   The base-restriction compatibility is inherited from the preceding datum's
   canonical transitions. Correct; no new localization or choice of charts.
10. The distinction from the base-change interface is preserved. I opened
    WeilConjectures/Compactification/ProjectiveSpace.lean and the defining
    ProjectiveSpace.lean: their arbitrary-base scheme is a pullback of the
    integral polynomial Proj, not this symmetric-sheaf relative-Proj datum.
    Reusing it would fail to express this node's specified interface.

Edge cases: r=0 uses Fin 1, so there is one coordinate, not an empty index set;
each degree then has one monomial. Degree n=0 has one constant monomial for any r.
There is no empty coordinate index in the node (r+1 is always positive). Empty
schemes, empty affine opens, zero section rings, and all characteristics remain
allowed: no Nontrivial, Nonempty, or field constraint occurs. Finite basis and
monomial indices are lifted to the scheme universe; no independent smaller test
universe or universe restriction is introduced. Local charts over a zero ring
are the corresponding empty schemes, which is consistent with the source.

Independent duplicate searches:

- LeanFinder via msearch: "Projective bundle of the trivial vector bundle on an
  arbitrary scheme via homogeneous coordinate charts". Eight hits: ordinary
  Proj, its standard chart isomorphisms, and vector-space projectivization;
  no symmetric-sheaf relative-Proj interface.
- Loogle via msearch: `"projectiveSpace"`. Zero hits.
- Grep via msearch: `ProjectiveBundle|projectivization|symmetric.*[Pp]roj`.
  Hits concern vector-space projectivization, not the requested scheme interface.
- LeanSearch via msearch: "Relative Proj of the symmetric algebra of a trivial
  finite locally free sheaf". Service unavailable (Internal Server Error);
  no mathematical verdict inferred from that failure.
- Independent rg of the project's algebraic-geometry modules and upstream
  ProjectiveSpace/Compactification sources found the existing base-change
  projective spaces and ordinary affine Proj. Reading their definitions
  confirmed that they do not give the node's relative-Proj construction datum.
  The dependency's RelativeProjAlgebra/RelativeProjData are reused directly;
  no second implementation of these notions is introduced.

No new nodes or dependency modules were delivered, so H12/H13 add no further
items to review. No mathematical mismatch, missing hypothesis, or hollow data
was found; I left the Lean and the node unchanged. Every new theorem has whole
proof `sorry` and a source-tagged proof plan; definitions contain no sorry data,
private copies, local instances, or file-local notation. The primary recorded
signature `def scheme : Scheme.{u}` is verbatim from the module, with X and r
bound by the namespace variables. All variables and the single universe u are
bound. The server scompile.py run passed cleanly: RelativeProjData 3.3 s,
RelativeProjExists 1.4 s, RelativeProjectiveSpace 2.5 s, each nice 19, two threads,
60 seconds per file. No local compiler or global build was run.
