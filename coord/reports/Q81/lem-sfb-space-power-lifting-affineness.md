## Worker report

The module `Sheaf.AlgebraicGeometry.SpacePowerLiftingAffineness` states
`AlgebraicGeometry.AlgebraicSpace.exists_affine_scheme_of_global_power_lifting`.
It contains one theorem with `sorry`, no new definitions, and no proved assertions.
Its docstring reproduces all six DAG proof steps and names every step's dependency.
The node's mathematical statement and its proof are unchanged.

Source read: Alper, *Adequate moduli spaces and geometrically reductive group schemes*,
journal version, Lemma 4.1.8(3) implies (2), printed pp. 502-504, and Theorem 4.3.1
and its proof, printed pp. 505-506, at
https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf . The former equates global
power lifting with adequate affineness; the latter identifies adequately affine
morphisms of algebraic spaces with affine morphisms. Neither place imposes a field,
Noetherian, or finite-type assumption for this assertion. The explicit scheme proof
and finite-cover/Chevalley reduction agree with the six steps of the node.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| R is an arbitrary commutative ring | `(R : Type u) [CommRing R]` |
| S = Spec R and Z is an algebraic space over S | `(Z : AlgebraicSpace (Spec (CommRingCat.of R)))`; this is the recorded full subcategory of fppf sheaves over S with representable diagonal and a surjective etale scheme atlas |
| Z admits a surjective etale atlas from a quasi-compact scheme | `_hqc : IsQuasiCompact Z.obj`; the recorded definition existentially quantifies `U : Over S` and `a : yoneda.obj U ⟶ Z.obj.obj` with `CompactSpace U.left`, `IsEtale a`, and `IsSurjective a` |
| The absolute diagonal is quasi-compact on affine scheme tests | `_hqs : MapIsQuasiCompact (prod.lift (𝟙 Z.obj.obj) (𝟙 Z.obj.obj))`; see the diagonal comparison below |
| Every pair of quasi-coherent commutative unital O_Z-algebras | `∀ (B C : Z.QCAlg)`; the existing `QCAlg` is the full subcategory of the under-category of the commutative structure sheaf whose underlying module satisfies Mathlib's `SheafOfModules.IsQuasicoherent` |
| Every algebra map B → C which is surjective as a sheaf | `(q : B ⟶ C), Presheaf.IsLocallySurjective Z.etaleTopology q.hom.right.hom →`; the map is in the under-category, hence respects the O_Z-algebra structures, and surjectivity is local lifting on a covering sieve |
| Every c in Gamma(Z,C) | `∀ c : (C.obj.right.obj ⋙ forget CommRingCat).sections`; `Functor.sections` is exactly the type of compatible families on all small etale charts |
| There is one integer N > 0 | `∃ N : ℕ, 0 < N ∧ ...`; N is chosen after B, C, q and c and before the chart U, so one exponent works globally |
| There is b in Gamma(Z,B) mapping to c^N | `∃ b : (B.obj.right.obj ⋙ forget CommRingCat).sections, ∀ U : Z.EtaleSiteᵒᵖ, (q.hom.right.hom.app U) (b.val U) = (c.val U) ^ N`; this is equality of compatible families on every chart, with the existing ring powers |
| Z is represented by an affine scheme | `∃ U : Over (Spec (CommRingCat.of R)), IsAffine U.left ∧ Nonempty (yoneda.obj U ≅ Z.obj.obj)`; the presheaf isomorphism is representability, over the same S |
| No Noetherian or finite-type assumption | No such binder occurs; R need not be nonzero, and neither Z nor a presenting atlas is required to be nonempty |

The presheaf product over `Over S` gives the relative diagonal Z → Z ×_S Z.
Since S = Spec R is affine and separated over Spec Z, its absolute diagonal is a
closed immersion. The absolute diagonal of Z is the composite of its relative
diagonal with the base change of this closed immersion. Conversely, the relative
diagonal is a base change of the absolute one. Thus quasi-compactness of these two
diagonals is equivalent. This uses precisely the existing affine-scheme-test
`MapIsQuasiCompact` definition, as reused by `MapIsQuasiSeparated` in the recorded
qcqs dependency; there is no extra separatedness assumption on Z. No statement
correction is needed for this equivalent expression over the specified affine base.

The existing global-sections primitive `CategoryTheory.Functor.sections` is used
directly, with equality evaluated on each chart. No independent choice of sections,
no new ring-of-global-sections definition, and no arbitrary algebra map is introduced.
Sheaf surjectivity is not replaced by surjectivity on global or all chart sections.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`
  (the latter read for the dependency's functorial interface).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, `IsRepresentableWith`, `IsEtale`, `IsSurjective`, `EtaleSite`,
  `etaleTopology`, `structureSheaf`, and `Modules`.
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`:
  `AlgebraicGeometry.AlgebraicSpace.IsQuasiCompact`, `MapIsQuasiSeparated`, and
  its reused `MapIsQuasiCompact` from `Sheaf.AlgebraicGeometry.ProperCurveModuli`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicGeometry.AlgebraicSpace.QCoh` and the slice sheafification instances;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsQuasicoherent` and `QuasicoherentData`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentAlgebra`:
  `AlgebraicGeometry.AlgebraicSpace.commStructureSheaf`, `CommAlgebraSheaf`,
  `CommAlgebraSheaf.toModule`, and `QCAlg`. This already-landed definition node,
  `def-sfb-space-quasi-coherent-algebra`, is added to `stmt_deps` rather than copied
  or redefined. Its statement, recorded declarations and full module were read.
- `Mathlib.CategoryTheory.Sites.LocallySurjective`:
  `CategoryTheory.Presheaf.IsLocallySurjective`.
- `Mathlib.CategoryTheory.Types.Basic`: `CategoryTheory.Functor.sections`.

All recorded, stated proof dependencies are imported without `public`, including
the higher-direct-image, affine-chart-calculus, module-operations, Zariski/etale
comparison, closed-subset ideal, symmetric-algebra, symmetric grading and
coproduct-cohomology modules. The Mathlib leaves are imported from the affine
morphism, residue-field, separation and symmetric-algebra basis modules.
The following proof dependencies currently have neither a Lean record nor a
Mathlib match and hence supply no module to import:
`lem-sfb-qcqs-space-finite-scheme-cover`, `lem-sfb-space-fp-qcqs-source`,
`lem-trf-symmetric-sheaf-map-degreewise-surjective`, and
`lem-sfb-finite-surjective-affine-space-target`. They are not notions required to
state this theorem, and the proof is left `sorry` as required for stage 2.

Edge cases checked before writing:

- The empty algebraic space is allowed. Its unique compatible sections satisfy
  lifting with exponent one and it is represented by the empty affine scheme
  Spec(0); the conclusion does not demand a nonempty affine representative.
- R may be the zero ring; the same empty-space case remains meaningful.
- N = 0 is explicitly excluded. Allowing it would make the lifting condition
  vacuous by using the unit for every section.
- Zero rings, zero algebra sheaves and zero sections are allowed; no nontriviality
  instance is used. For a zero section its power can be lifted by zero with N = 1.
- Disconnected spaces impose one common global exponent, not chart-dependent
  exponents; this follows from the quantifier order of the written signature.
- Projective space does not make the hypothesis vacuous: on P^1 over a field,
  O(-1)^2 → O is surjective, hence so is its symmetric-algebra map to O[t],
  while all positive symmetric-degree sections of the source vanish. The target's
  global section t has no positive-power global lift. Thus a standard nonaffine
  qcqs scheme fails the hypothesis as expected.
- The site retains objects in universe u+1, morphisms and chart rings in universe
  u. Global compatible families may live in universe u+1; the statement does not
  force them into u or introduce a smaller independent universe for test objects.

Searches actually run (msearch.py, group Q81 and this item, on 2026-10-24):

1. LeanFinder: `A quasi compact quasi separated algebraic space is affine when every global section of every quotient quasi coherent algebra has a positive power lifting globally`.
   Eight hits: scheme quasi-separatedness/quasi-compactness instances, quasi-affine
   predicates and criteria, and a cofiltered-limit quasi-affine lemma. None states
   global power-lifting affineness for algebraic spaces.
2. Loogle: `"AlgebraicGeometry", "IsAffine"`.
   Twelve hits: `IsAffine`, `IsAffineOpen`, spectra and affine-scheme instances,
   and affine invariance under isomorphisms. These give the conclusion's predicate,
   but no theorem matching this item.
3. Mathlib grep: `adequat|power.?surject|power.?lift`, subdirectory `AlgebraicGeometry`.
   Zero hits.
4. LeanSearch: `A quasi compact quasi separated algebraic space with global power lifting for every surjection of quasi coherent algebras is represented by an affine scheme`.
   Eight hits: the quasi-affine basic-open criterion, scheme quasi-separatedness
   criteria, `IsAffine.casesOn`, and affine-scheme instances. No exact match.
5. `rg` in `lean/WeilConjectures/AlgebraicGeometry` and
   `lean/Sheaf/AlgebraicGeometry` for `power.?lift|adequat|QCAlgebra|QuasiCoherentAlgebra`,
   followed by focused reads of the space algebra modules and adequate-affineness
   interfaces. This located the existing `QCAlg`; the stack global-power criteria
   are over fields and have a different conclusion, so cannot serve as this theorem.
6. `rg` in all of `lean/WeilConjectures` and `lean/Sheaf` for the item id:
   no existing statement. `rg` for `exists_affine_scheme_of_global_power_lifting`
   in both roots, Mathlib and `dag/lean_names_upstream.json`: no name collision.
7. DAG node read for `def-sfb-space-quasi-coherent-algebra`: the notion is already
   recorded and landed. No new definition node is necessary.

Validation: scompile.py compiled both its sandbox check and the actual library
module successfully (40.7 s and 10.7 s), with no non-sorry warning or error.
`autoImplicit` is false, and the only universe is explicitly declared `u`.
Every Lean source line is at most 100 characters. No node fault or unresolved
statement dispute was found.

## Second reading by Q81

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
