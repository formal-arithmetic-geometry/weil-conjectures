## Worker report

States `AlgebraicGeometry.exists_torus_invariant_affine_filtration` in
`Sheaf.AlgebraicGeometry.TorusInvariantAffineFiltration`. There is one theorem,
with proof `sorry`, and no new definitions. The accepted natural-language statement
and eight-step split are preserved. The existing landed definition node
`def-sfb-tori-multiplicative-type` is added to stmt_deps for its actual split torus.

The inherited BLOCKED ending concerns a stage-1 reopening gate. The current node is
stage-1 reviewed/pass with no Lean attachment and appears as a stage-2 item in the
queue. The stage-2 brief §0 explicitly authorizes this handoff. No repair note was
found for this item. The local CompactObject example has been withdrawn; its node
now points to the upstream definition, so the new module follows current module-mode
conventions instead.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Algebraically closed field F: `(F : Type u) [Field F] [IsAlgClosed F]`.
- Nonnegative rank: `(r : ℕ)`, including zero. The group scheme is
  `T : Grp (Over (Spec (.of F)))`, with
  `hT : Nonempty (T ≅ MultiplicativeType.splitTorus F r)` an isomorphism of group
  schemes. This is the existing product of the Laurent-polynomial multiplicative
  group, with the tensor unit as the empty product. Its group law represents units
  on arbitrary commutative F-algebras, including nonreduced ones.
- T acts on Y: Y is a `CategoryTheory.Mod (Over (Spec (.of F))) T.X`.
  Its stored `ModObj` action is an actual scheme map with unit and associativity
  diagrams. This does not replace the algebraic action with an action on F-points.
- Separated finite-type Y: `[IsSeparated Y.X.hom]`,
  `[LocallyOfFiniteType Y.X.hom]`, `[QuasiCompact Y.X.hom]`.
- Invariant open V: V is another module object and `j : V ⟶ Y` is an equivariant
  arrow, with `[IsOpenImmersion j.hom.left]`. This is precisely the restricted
  action and equivariant open inclusion specified by the node.
- Separated finite-type V: the first three conjuncts are `IsSeparated V.X.hom`,
  `LocallyOfFiniteType V.X.hom`, and `QuasiCompact V.X.hom`.
- Reduction and induced action: existential module object R and equivariant arrow
  `i : R ⟶ V`, with `IsReduced R.X.left`, `IsClosedImmersion i.hom.left`,
  `i.hom.left.ker = Scheme.IdealSheafData.vanishingIdeal ⊤`, and
  `Set.range i.hom.left = Set.univ`. On affine charts the displayed ideal is the
  intersection of all primes, hence the nilradical. The closed immersion and full
  image identify its underlying space with V. These conditions specify the actual
  reduction up to unique isomorphism over V; no arbitrary closed thickening is used.
- Finite descending chain: `N : ℕ`, `Z : Fin (N + 1) → ...`,
  `inclusion : ∀ a : Fin N, Z a.succ ⟶ Z a.castSucc`, and the condition that every
  inclusion is a closed immersion. `Z 0 = R` and
  `IsEmpty (Z (Fin.last N)).X.left` are the two endpoints.
- Invariant reduced closed terms: every Z is a module object, each arrow is
  equivariant by its type, and `∀ a, IsReduced (Z a).X.left ∧ ...` gives reducedness.
  Composing adjacent closed equivariant arrows realizes every term as a closed
  equivariant subscheme of R. Inclusions into V and Y are their composites with i,j.
- The open complement S_j: `S : Fin N → ...` and
  `stratum : ∀ a, S a ⟶ Z a.castSucc`; its underlying arrow is an open immersion
  and its range is exactly `(Set.range (inclusion a).hom.left)ᶜ`.
  Thus this is the scheme-theoretic open complement, not merely a disjoint subset.
  Its action and equivariance are again in the module objects and arrows.
- Affine strata: `IsAffine (S a).X.left` for every `a : Fin N`.
- Separatedness and finite type of all Z and S: the corresponding `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact` conjuncts for their structural morphisms.
- All inclusions equivariant: all j, i, inclusion and stratum arrows live in the
  category of module objects. Their composites give the remaining inclusions.
- Empty V: at N=0 the single chain member is simultaneously R and the empty
  endpoint; Fin 0 has no strata or arrows. No nonemptiness or positive-length
  condition occurs. No normality, smoothness, projectivity, effectiveness, or
  characteristic hypothesis has been introduced.

Dependencies read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.FieldTheory.IsAlgClosed.Basic` and `.AlgebraicClosure`: `IsAlgClosed`
  (the relevant algebraically-closed clause of def-weil-algebraic-closure).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp` (def-sc-group-scheme).
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom` (def-pc-scheme).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` / `.Separated`: `IsSeparated`
  (the separated clause of def-weil-proper-morphism; properness is not assumed).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` / `.QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact` (def-weil-finite-type-morphism).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`
  (def-weil-open-immersion).
- `Mathlib.AlgebraicGeometry.Properties`: `IsReduced` (def-pc-reduced-scheme).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`
  (def-weil-closed-immersion).
- `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine`, `Spec`
  (def-weil-affine-spectrum, available through recorded scheme imports).
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `AlgebraicGeometry.MultiplicativeType.splitTorus`, in the added landed definition
  dependency; its existing `StandardGroupSchemes.multiplicative` is not redefined.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Mod` and `.Monoidal.Mod`:
  `ModObj`, `Mod`, `IsModHom`, `Mod.Hom`. These supply the existing action notion.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic` / `.Subscheme`:
  `Scheme.IdealSheafData.vanishingIdeal`, `Scheme.Hom.ker`. The recorded proof
  dependency `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`,
  `AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`,
  explains exactly this reduced ideal and its unique reduced closed scheme.

Every currently recorded Lean proof-dependency module is imported with plain import:
GeometricReducedFiniteTypePerfectField, SlicingFlat, LfpSmoothFlatBaseChange,
ClosedImmersionProducts, ReducedInducedClosedSubscheme, the upstream Mathlib
ClosedImmersion extension, Regular, and RegularNormalDecomposition. Proof dependencies
without a Lean module are named in the proof docstring for stage 3; no new proof
statements are invented. There is no dependency repair or new node.

Edge cases checked before writing: rank zero is the trivial torus and still allows
ordinary affine stratification. Empty V permits N=0, and every finite index expression
remains meaningful. A nonreduced Y, for example dual numbers with trivial action,
is allowed; the theorem reduces V rather than assuming it reduced. A singular
non-normal reduced scheme is allowed; normality occurs only on the intermediate
open used in the natural-language proof. Ineffective/trivial actions and positive
characteristic are allowed. The common universe u is the standard universe of
F-schemes; no independent smaller test-algebra universe or field-point test is used.

Searches (msearch output is preserved in searches.jsonl in the sandbox):

- LeanFinder: "A split torus acting on a separated finite type scheme has a finite
  invariant reduced closed filtration with affine strata": 8 hits, ordinary affine
  covers and unrelated quotient decomposition, no invariant torus filtration.
- Loogle: `AlgebraicGeometry.Scheme, "filtration"`: 0 hits.
- Mathlib grep: `Sumihiro|torus.*filtration|invariant.*affine`: 2 unrelated convex
  analysis hits, no match.
- LeanSearch: "A split torus acting on a separated scheme has invariant affine
  locally closed strata": 8 hits, separatedness and quasi-affine facts, no match.
- Project rg for `torus_invariant_affine`, `Sumihiro`, actions, torus and filtration
  notions in WeilConjectures and Sheaf: no existing theorem. The broader search
  found the existing splitTorus, ModObj, and a smooth affine filtration with extra
  smooth/geometrically connected clauses that does not encode torus invariance.
- Exact item-id search in WeilConjectures and Sheaf returned no theorem.

No statement correction or STATEMENT-DISPUTED issue. The source is honestly
agent-formulated, and the WANTED Sumihiro input remains explicit in the docstring.
The current blueprint unit was read and is not changed.

Validation: scompile.py compiled the sandbox and final module successfully,
with no errors or unexpected warnings, before the delivery dry run.

## Second reading by Q68

No second worker was started, as the dispatcher explicitly forbids subagents.
The maintainer supplies the independent review under the current direct-delivery
workflow. The clause correspondence above is the worker's own reading.
