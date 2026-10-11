## Worker report

The module `Sheaf.AlgebraicGeometry.ConstructibleCurveSubQuotient` states
`AlgebraicGeometry.CurveCoefficientPair.constructible_sub_quotient`, with one theorem
and `sorry` as its proof. It introduces no definition, instance, or auxiliary theorem.
Only the item's `lean` field changes. No statement correction or new node is needed.

Hypothesis and conclusion correspondence:

- Algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- Separated finite-type scheme C over k with dimension at most one: the recorded
  `P : AlgebraicGeometry.CurveCoefficientPair k` supplies `P.C`, `P.toSpec` and
  `P.isCurve : IsCurve P.toSpec`. Read in the source, `IsCurve` extends
  `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`, with
  `topologicalKrullDim P.C ≤ 1`. No smoothness, connectedness or properness is imposed.
- The abelian sheaf F: `P.F : Sheaf P.C.smallEtaleTopology AddCommGrpCat.{u + 1}`.
  The outer sheaves F_1 and F_2 are the binders `F₁ F₂` in the very same category.
- All three terms torsion, hence curve coefficient pairs: `P.isTorsion` supplies
  torsion of F, and `h₁`, `h₂` supply torsion of the outer terms using the
  recorded pair's `Scheme.IsTorsionAbelianSheaf` predicate. This is the colimit
  of positive-integer torsion kernels convention of `def-weil-pbc-torsion-etale-sheaf`,
  used by the dependency itself; in a sheaf category it expresses locally torsion
  sections, as does the source `CategoryTheory.Sheaf.IsTorsion`. We do not impose
  that every group of sections is torsion, nor an annihilator or characteristic bound.
- Maps alpha and beta: `(α : F₁ ⟶ P.F) (β : P.F ⟶ F₂)` are natural transformations
  of abelian sheaves. The datum `(w : α ≫ β = 0)` allows `ShortComplex.mk α β w`.
  It is already implied by a short exact sequence, not an additional restriction.
- The short exact sequence: `hS : (ShortComplex.mk α β w).ShortExact`; Mathlib's
  definition is exactness at F, monicity of alpha and epicity of beta, precisely
  the two endpoint zeros and middle exactness in the node.
- F constructible: `hF : P.IsConstructible`, the exact dependency declaration.
  Its body forgets the abelian group structure and uses
  `Scheme.IsConstructibleEtaleSheafOfSets`, a finite stratification with
  constructible locally closed subschemes and finite locally constant restrictions.
- F_1 constructible: the first conjunct uses `CurveCoefficientPair.IsConstructible`
  on `{ P with F := F₁, isTorsion := h₁ }`. It keeps exactly P's curve and base map.
- F_2 constructible: the second conjunct uses the same predicate on
  `{ P with F := F₂, isTorsion := h₂ }`. The conclusion contains both assertions,
  with no claim of constructibility in the reverse direction.

Dependencies read and used:

- `def-weil-algebraic-closure`: `IsAlgClosed`, in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, provided through the curve import.
  The node's match also records `AlgebraicClosure` / `IsAlgClosure`; these are not
  needed to introduce an already algebraically closed k.
- `def-weil-pbc-abelian-etale-sheaves`: `CategoryTheory.Sheaf`, in
  `Mathlib.CategoryTheory.Sites.Sheaf`, specialized to the recorded
  `AlgebraicGeometry.Scheme.smallEtaleTopology` and `AddCommGrpCat`.
  Read `Sheaf` and `smallEtaleTopology` at their actual source signatures.
- `def-weil-pbc-etale-sheaves`: read
  `Sheaf.AlgebraicGeometry.EtaleSheaves` in full, and the full docstring and signature
  of `CategoryTheory.Sheaf.IsTorsion` in
  `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.
  Its constructibility predicate for sheaves of sets is used by the recorded
  curve-specific `IsConstructible`, through the imported dependency.
- `def-weil-pbc-curve-setting`: `AlgebraicGeometry.CurveCoefficientPair`, in
  `Sheaf.AlgebraicGeometry.CurveCoefficientPair`, read in full together with
  the source `IsCurve` and the pair's `IsTorsionAbelianSheaf` definition.
- `def-weil-pbc-constructible-torsion`: `AlgebraicGeometry.CurveCoefficientPair.IsConstructible`,
  in `Sheaf.AlgebraicGeometry.ConstructibleTorsionCurveSheaf`, imported directly.
- The other direct import is `Mathlib.Algebra.Homology.ShortComplex.ShortExact`.
  Its `ShortExact` docstring and fields, and `ShortComplex` in `Basic`, were read.

Edge cases checked before writing: C can be empty (dimension is bottom, hence at
most one), zero-dimensional, reducible, nonreduced, disconnected or nonproper.
F and either outer sheaf can be zero, and the sequence can split. The finite
stratification predicate permits the empty partition on the empty scheme.
There is no characteristic restriction and no prime-to-characteristic hypothesis.
The universe u is explicit; schemes, fields, sheaves and pairs use exactly the
universes of the recorded dependencies, with abelian groups in `u + 1`.
All morphisms are in the abelian sheaf category, not the set-sheaf category or a
fixed-coefficient module category. The statement is mathematically consistent
with these cases; no `STATEMENT-DISPUTED` issue was found.

Source checked: local `literature/stacks-project/etale-cohomology.tex` is absent
on this machine, so opened https://stacks.math.columbia.edu/tag/09BH and
https://stacks.math.columbia.edu/tag/095E. Proposition 09BH (2) explicitly gives
subobject and quotient constructibility in the abelian sheaf category on a
Noetherian scheme. Lemma 095E identifies constructibility with the global finite
partition on the quasi-compact quasi-separated scheme. The module docstring
carries all six node proof steps, including the finite-annihilator argument,
module bridge, subobject result, cokernel result and return to the curve notion.

Searches (all run for this item):

- `msearch.py ... leanfinder "subsheaves and quotient sheaves of a constructible torsion abelian etale sheaf on a curve are constructible"`:
  eight hits on unrelated scheme sections, etale loci, O-module categories and
  finite-type O-module sheaves; no constructible abelian-sheaf result.
- `msearch.py ... loogle "IsConstructibleSheaf, ShortComplex.ShortExact"`:
  zero hits, unknown identifier `IsConstructibleSheaf` in Mathlib.
- `msearch.py ... grep "IsConstructibleSheaf|constructible.*[Ss]heaf"`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Subobjects and quotients of constructible abelian sheaves on a Noetherian scheme are constructible"`:
  service unavailable, Internal Server Error; not treated as a negative result.
- `rg` in the source and `lean/Sheaf` for constructible subobject/quotient and
  short-exact statements: found
  `AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_shortExact` in
  `WeilConjectures.ConstructibleSheaf.KernelCokernel` (full docstring and signature
  read). It asserts constructibility of the middle term from constructible outer
  terms for module sheaves over a finite ring, so it is not this statement.
  `ConstructibleSubsheafNoetherian` concerns fixed-coefficient module sheaves;
  it is already a proof dependency, not the torsion-abelian curve statement.
  The source curve `IsCurve.Assertions.of_shortExact` is about C1-C8 assertions
  of fixed-coefficient sheaves, not this constructibility implication.
- Search for the item's id in the source: no hits.
- Search for the chosen name `constructible_sub_quotient` in Mathlib, source,
  project Lean and `dag/lean_names_upstream.json`: no hits.

Validation: server single-file compilation completed cleanly with exit code 0
in 1.8 seconds. Only the permitted theorem proof is `sorry`. No local build,
repository edit or direct git command was performed. Delivery dry run is the
final check; the second reader supplies the independent reading and delivery.

## Second reading by E1

Independent verdict: the statement matches the node clause by clause. No Lean or
node repair is needed; this reading adds the independent review only.

Source reading: the repository has no Stacks checkout. I downloaded the source
`etale-cohomology.tex` from https://raw.githubusercontent.com/stacks/stacks-project/master/etale-cohomology.tex
into the sandbox scratchpad and read `definition-constructible` (03RW),
`lemma-constructible-quasi-compact-quasi-separated` (095E), the opening paragraph of
`section-noetherian-constructible`, `proposition-constructible-over-noetherian`
(09BH), and `lemma-ses-statements` (0A5C), including their proofs. I also checked
[09BH](https://stacks.math.columbia.edu/tag/09BH),
[095E](https://stacks.math.columbia.edu/tag/095E),
[03RW](https://stacks.math.columbia.edu/tag/03RW), and
[0A5C](https://stacks.math.columbia.edu/tag/0A5C).
09BH assumes a Noetherian scheme (the Noetherian coefficient ring concerns its
module clause); finite type over the field gives this here. The finite global
partition agrees with the affine-local notion by 095E. The geometric hypotheses
in 0A5C are exactly the curve hypotheses in this node. Its proof uses both
directions of constructibility, but this node intentionally supplies only the
middle-to-outer direction; the Lean does exactly that.

The node's objects, hypotheses, and conclusions, listed before comparison:

| Node item | Lean rendering and verdict |
| --- | --- |
| An algebraically closed field k | `{k : Type u} [Field k] [IsAlgClosed k]`; exact. Mathlib's `IsAlgClosed` says all polynomials split, equivalently the root definition of the dependency. |
| A scheme C over k | `P : AlgebraicGeometry.CurveCoefficientPair k`, with `P.C` and `P.toSpec : P.C ⟶ Spec (.of k)`; exact. |
| C separated, finite type, dimension at most one | `P.isCurve : IsCurve P.toSpec`; exact. I opened `WeilConjectures/AlgebraicGeometry/Curve.lean`: the class extends `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, and adds `topologicalKrullDim P.C ≤ 1`. No hidden smoothness, connectedness, reducedness, or properness. |
| Three abelian sheaves on the same small etale site | `P.F`, `(F₁ F₂ : Sheaf P.C.smallEtaleTopology AddCommGrpCat.{u + 1})`; exact. I opened Mathlib's actual `Sheaf` and `smallEtaleTopology`: a full subcategory of sheaf presheaves on schemes etale over C. |
| All three sheaves torsion | `P.isTorsion`, `h₁`, `h₂` in `P.C.IsTorsionAbelianSheaf`; exact. I read the curve-pair and torsion modules. The canonical colimit of positive-integer torsion kernels is F, expressing locally killed sections; this is equivalent to the local-section `CategoryTheory.Sheaf.IsTorsion` in the etale-sheaves dependency, whose body I also read. No uniform annihilator or global-section torsion is assumed. |
| Alpha and beta in the abelian sheaf category | `(α : F₁ ⟶ P.F) (β : P.F ⟶ F₂)`; exact natural transformations with these endpoints. |
| Short exact sequence including both endpoint zeros | `(w : α ≫ β = 0)` and `(hS : (ShortComplex.mk α β w).ShortExact)`; exact. I read Mathlib's fields: middle exactness, `Mono α`, `Epi β`. The proof of zero composition is inherent in the sequence, with no stronger mathematical hypothesis. |
| F constructible with a finite locally closed constructible partition and finite locally constant restrictions | `(hF : P.IsConstructible)`; exact. I read `ConstructibleTorsionCurveSheaf.lean`, `EtaleSheaves.lean`, and source `Stratification`: the predicate forgets groups to sets, uses actual etale inverse image to each immersed stratum, and finite geometric stalks. Finite group local constancy is equivalent to the underlying finite-set version. |
| F1 constructible on the same curve | First conjunct `CurveCoefficientPair.IsConstructible { P with F := F₁, isTorsion := h₁ }`; exact, preserves C, base map and curve proof. |
| F2 constructible on the same curve | Second conjunct with `F₂`, `h₂`; exact, same base data and same notion. Both conclusions occur together under the original quantifiers. |

I opened every direct statement dependency node and its recorded declaration or
Mathlib match, rather than trusting the worker's descriptions. None needs a
replacement module. There are no new nodes, dependency modules, or statement
corrections in this delivery, so H12/H13 and corrected-citer checking do not apply.

Edge cases: empty C is allowed by `topologicalKrullDim = ⊥`; no nonemptiness is
required by the pair. The source `Topology.Stratification.n : ℕ` permits n = 0,
with `Fin 0`, exactly for the empty underlying space. All three sheaves may be
zero, and either outer sheaf may vanish; mono/epi and short exactness express the
expected degeneracies. C may be zero-dimensional, disconnected, nonreduced,
reducible, or nonproper. No characteristic or prime-to-characteristic constraint
is present. There is no theorem-level integer n or index set to restrict. Universe
u is bound explicitly; the site, field, schemes, and test geometric fields use u,
and abelian sheaf values use u + 1, exactly the dependency convention. This is
not the vacuous independent lower test-universe pattern. Larger data can be put
in a common larger universe. No variable or universe is unbound.

Independent searches, with different phrasing from the worker:

- LeanFinder: `finite stratification abelian sheaf stable under subobjects and quotients`:
  eight hits, chiefly abstract `ObjectProperty.IsSerreClass` and Grothendieck
  abelian sheaf categories; no theorem about this constructibility predicate.
- Loogle: `ShortComplex.ShortExact`: reports unknown identifier, zero hits;
  this remote lookup is not evidence that the local declaration is missing.
- LeanSearch: `A finite locally constant stratified abelian sheaf has constructible subobjects and quotient sheaves`:
  unavailable (Internal Server Error), recorded without a negative verdict.
- Direct `rg` on Mathlib, the source `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for constructibility with sub/quotient,
  `of_shortExact`, kernel/cokernel, and the proposed name. Opened
  `IsConstructibleSheaf.kernel`, `.cokernel`, `.of_shortExact` in
  `ConstructibleSheaf/KernelCokernel.lean`. These concern fixed-ring module
  sheaves; kernel/cokernel require constructible source and target, and
  `of_shortExact` concludes the middle from outer terms. They do not state this
  theorem. Opened `isConstructibleEtaleModuleSheaf_of_mono_noetherian` in
  `ConstructibleSubsheafNoetherian.lean`: it is the fixed finite-ring module
  subobject proof dependency, not the abelian curve result. The chosen full name
  has no duplicate in the libraries or upstream name map.

H5/H6/H8/H9: the file introduces only the named theorem with proof `by sorry`,
no data definition or private notion. Its module and declaration docstrings name
the source and blueprint; the six proof steps follow the node: common annihilator,
module bridge, constructibility comparison, subobjects, cokernels, return to the
curve notion. Both imports serve actual declarations in the signature. All lines
are at most 100 characters. Namespace and file path follow the contract.
The node's `lean.statement` is byte-for-byte equal to the source signature before
`:=`. No mismatches were found; Lean and node were left unchanged.

Validation: independent server single-file compile via `scompile.py` exited 0 in
1.9 seconds with no warnings. The initial relative file argument was resolved
from the read-only repository and failed to find the sandbox file; rerunning with
the absolute sandbox path succeeded. This was an invocation error, not a Lean
error or a tool defect. Delivery preflight and push are run after this report.
