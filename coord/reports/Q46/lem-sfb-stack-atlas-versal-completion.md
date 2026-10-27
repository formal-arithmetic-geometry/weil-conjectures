## Worker report

The module `Sheaf.AlgebraicGeometry.StackAtlasVersalCompletion` states
`CategoryTheory.StackVersal.exists_atlas_versal_completion`, with `sorry` as its
proof. Its helper `completionToScheme` explicitly constructs the map from the
identified maximal-ideal completion of the stalk to the atlas scheme. Its data
are actual Mathlib ring maps and scheme maps; no existence choice is used.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The commutative Noetherian local base is `R : Type u` with `CommRing`,
  `IsLocalRing`, and `IsNoetherianRing`. The field `k` has its R-algebra structure,
  algebra structure over `IsLocalRing.ResidueField R`, scalar tower, and
  `Module.Finite` over that residue field. Thus the given finite extension is
  compatible with the specified R-point; no separability is imposed.
- `F : BasedCategory.{v,w} (Over (Spec R))` with `hF : IsAlgebraicModuliStack F`
  uses exactly the recorded fibred-groupoid, effective etale descent,
  algebraic-space diagonal and smooth-surjective-atlas definitions. The universe
  levels `u v w` are explicit. `hft` is a smooth atlas whose structural map is
  `LocallyOfFiniteType`, exactly the node's stack local-finite-type condition.
- `x : Object F k` is the given k-point in its actual fibre. `U`, `p` and
  `hp : IsSmoothModuliAtlas F U p` specify the given smooth surjective scheme
  atlas, including its actual base-change projections.
- The existential `Ω : OpenModuliSubstack F` is smooth, and every smooth open
  `W` is `IsContainedIn Ω`. This states that Ω is the largest smooth open,
  without selecting one from an unconstrained existence theorem.
- `V : U.left.Opens`, `B : CommAlgCat R`, `eV : Spec B ≅ V.toScheme`,
  `Algebra.FiniteType R B`, and the structure-map equality state the affine
  finite-type R-algebra neighbourhood in the chosen atlas. No affine
  presentation unrelated to U or to its R-structure is allowed.
- `z : U.left` and `hz : z ∈ V` are the point. Its field is literally
  `U.left.residueField z`. The R- and residue-base algebra structures, scalar
  tower and `Module.Finite` express finiteness over R/m_R. The map `j₀` equals
  `U.left.fromSpecResidueField z`; since j₀ is over Spec R, this also fixes its
  R-structure. `x₁` with `s` over j₀ identifies the point p(z) in the stack.
- The field `l` has compatible k- and R-algebra structures and `Module.Finite k l`.
  The R-algebra map `i : kappa(z) →ₐ[R] l` is an embedding because its source is
  a field, and `i.toRingHom.Finite` states l/kappa(z) finite. `xl` has cartesian
  `Arrow`s along k→l and i to x and x₁, respectively. These two identifications
  are precisely the common-field isomorphism p(z)|l ≅ x|l.
- `C : CompleteLocalAlgebra R (U.left.residueField z)` supplies the complete
  Noetherian local R-algebra and its specified residue isomorphism. `e` identifies
  its ring with the actual `AdicCompletion` of `U.left.presheaf.stalk z` at its
  maximal ideal. The map j is over Spec R and equals `completionToScheme ... e`;
  this fixes the R-algebra structure on that completion. The equation involving
  `C.residueEquiv` fixes the canonical residue identification by equality of
  the induced scheme maps with j₀.
- `η : FormalObject F x₁ C` uses the existing total-category marked tower, whose
  levels n mean C/m^(n+1). It includes objects, transition arrows for all ordered
  pairs of levels, their unit and composition equations, and residue markings
  compatible with these arrows. `a` is the quotient map followed by j at every
  level; `t` lies over a, commutes with all transitions, and composes with the
  markings to s. Thus this is the formal object pulled back from the given p,
  not an arbitrary versal object on an isomorphic ring.
- `η.IsVersal` is the existing full marked lifting predicate. It quantifies over
  all surjections of Artinian local R-algebras with specified residue field,
  local residue-preserving C-maps, marked objects, and the prescribed
  isomorphism. Its lifted algebra map restricts to the original one, and its
  final arrow equation preserves exactly that isomorphism. Evaluation is by
  finite quotients, and its common-higher-level formulation retains every test.
- The final equivalence `Ω.property x.val ↔ ∃ W : V.toScheme.Opens, ...`
  states membership of x in the largest smooth open exactly when V→Spec R is
  smooth on an open neighbourhood W of the point `⟨z,hz⟩`.

Recorded dependency interfaces read and used:

- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`;
  `Mathlib.Algebra.Field.Defs`, `Field`;
  `Mathlib.AlgebraicGeometry.Scheme`, `Scheme`, `Spec`, `Spec.map`;
  `Mathlib.AlgebraicGeometry.ResidueField`, `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`;
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `LocallyOfFiniteType`;
  `Mathlib.RingTheory.AdicCompletion.Basic`, `AdicCompletion`, and its ring
  structure from `Mathlib.RingTheory.AdicCompletion.Algebra`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`, `AlgebraicSpace` and its
  representability predicates, through the stack interface. The size-convention
  dependency has no mathematical declaration and is rendered by universes.
- Added already-landed statement dependencies:
  `def-sfb-algebraic-moduli-stack`, using `IsAlgebraicModuliStack`,
  `IsSmoothModuliAtlas`, `IsSmoothModuliStack` in
  `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`;
  `def-sfb-open-moduli-substack`, using `OpenModuliSubstack`, `.category`, and
  `.IsContainedIn` from `Sheaf.AlgebraicGeometry.OpenModuliSubstack`;
  `def-sfb-formal-moduli-quotient`, using `CategoryTheory.moduliChartPoint`
  from `Sheaf.AlgebraicGeometry.FormalModuliQuotient`;
  `def-sfb-stack-versal-formal-object`, owning the existing public auxiliary
  `StackVersal.Object`, `Arrow`, `CompleteLocalAlgebra`, `Level`, `FormalObject`,
  and `FormalObject.IsVersal`. The extension theorem itself is not assumed.
  The new definition node records these exact existing declarations; it does not cite or use the finite-residue-extension theorem.
- Available proof dependency imports are
  `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus` and
  `Sheaf.AlgebraicGeometry.ArtinLocalTestAlgebra`. The test-category definition
  is supplied transitively by the latter. Other proof-only nodes have no
  recorded modules and are named in the complete natural-language proof
  docstring rather than given duplicate statements.

The source paragraphs read were Stacks `stacks-geometry.tex`,
`lemma-compare-versal-ring-completion` (0DQZ), especially (4) and the final
assertion; `lemma-characterize-smoothness` (0DZS), final paragraph; and
`stacks-morphisms.tex`, `lemma-where-smooth` (0DZR), existence and clause (1).
The module docstring and theorem proof follow the node's six proof steps,
including preservation of the prescribed marked isomorphism.

Edge cases checked: an empty atlas cannot admit the common-field lift of the
supplied field-valued point; no artificial nonemptiness assumption was added.
The chosen V contains z, as required. A field base R and zero-dimensional atlas
points are allowed; no positive dimension is imposed. Quotient levels start
at exponent 1, and zero maximal ideal is allowed. Surjections that are
isomorphisms occur in the versality tests and use the inverse directly. Finite
inseparable extensions are included, with no characteristic assumptions.
Sites and test rings live in the same scheme universe, so the quantification
is not vacuous due to a smaller test universe.

Searches (2026-10-24):

- `msearch.py leanfinder`: “A smooth atlas of an algebraic stack gives a versal
  completed local ring at a point”: eight scheme-smoothness hits, no stack theorem.
- `msearch.py loogle`: `AdicCompletion, IsLocalRing, AlgebraicGeometry.Smooth`:
  zero hits.
- `msearch.py leansearch`: “smooth scheme atlas completion versal ring algebraic
  stack”: eight hits on formal smoothness and scheme smoothness, no exact match.
- `msearch.py grep`: `versal|AlgebraicStack` in Mathlib AlgebraicGeometry:
  unrelated universal-property mentions, no exact theorem.
- `rg` in `lean/WeilConjectures` for this node ID: no hit; for versal/completion
  terminology in its algebraic geometry modules: no matching theorem.
- `rg` in `lean/Sheaf/AlgebraicGeometry` found the existing stack and formal-object
  interfaces above, and `moduliChartPoint`, which is reused. No atlas-completion
  theorem was found. Searches for `completionToScheme` and the main declaration
  name in Mathlib, WeilConjectures, Sheaf and `dag/lean_names_upstream.json`
  found no existing declaration.

No statement correction, dependency replacement module, or statement dispute. The ownership repair adds the definition node described below.
The example CompactObject module is currently withdrawn (no declarations); its
node's existing record was read, and current public module conventions are used.

Validation: server `scompile.py` compiled the delivered module in sandbox and
library mode without errors or unexpected warnings.

## Second reading by Q46

The dispatcher explicitly prohibits starting another agent; this is my separate
second pass over the node and the final signature, with the maintainer's independent
review still required. I checked every hypothesis and each existential witness
against the source and the clauses listed above. I replaced a prospective helper
for the atlas identity object by the existing `moduliChartPoint` to avoid a
second definition. The completion's R-structure and residue identification are
fixed by scheme-map equalities. The formal object's arrows to the atlas are
required to commute with every transition and marking, and the imported versality
predicate preserves the prescribed isomorphism. The smoothness test uses an open
of V itself. No mathematical statement mismatch was found; no weakening or extra
finiteness/separability assumption was introduced.


## New nodes

`def-sfb-stack-versal-formal-object` registers the exact existing stack interface in
`Sheaf.AlgebraicGeometry.StackVersalFiniteResidueExtension`, with `existing: true`
and an ownership note. Its main declaration is `StackVersal.FormalObject.IsVersal`;
its declaration list owns all thirteen existing supporting definitions, from
`affine` through `FormalObject.IsVersal`. The source is Stacks 0DQY and the marked
formal-object/versal definitions in 06HR and 06HS. No Lean definition is duplicated.
The node states the fibres and arrows over affine test maps, the complete marked
local algebra, all positive quotient levels, coherent transitions and markings,
and the full prescribed-isomorphism lifting predicate. The exact Lean declarations
and docstrings were reread. CompleteLocalAlgebra supplies precisely its local,
Noetherian, complete and residue-equivalence clauses; FormalObject supplies its
objects, transition_id, transition_comp and mark_transition clauses; IsVersal
supplies the arbitrary Artinian surjection, local marked maps, lifted ring map,
and equality preserving the prescribed marked identification at a common level.
The general definition can be written for a category over schemes; its pullback
interpretation is used when it is fibred in groupoids, as it is in this item.

New searches on 2026-10-24 used LeanSearch for the full marked formal-object
lifting condition (8 ring-formal-smoothness hits), LeanFinder for “versal marked
formal object complete local ring stack” (8 scheme/ring hits), and Mathlib grep
`FormalObject|IsVersal|CompleteLocalAlgebra` (zero hits). Their exact outputs are
recorded in the new node. DAG, upstream and Sheaf grep plus blueprint_refs search
found the exact theorem-module auxiliaries but no definition-node owner.
ArtinDeformationTestCategory uses chosen cofibred transport data and therefore
has a different formal-object interface. This delivery records the existing
stack declarations, as allowed for a new definition node, instead of copying them.

## Repair of returned H2

Compared the saved packet with returned head 2e3e5dbebc92 as described in the
return and with current main: the theorem signature and mathematical node
statement are preserved. Main still has no Lean record for this item, so its
original dependencies remain intact. The saved addition of the theorem node
`lem-sfb-stack-versal-finite-residue-extension` was removed and replaced by
`def-sfb-stack-versal-formal-object`. The new definition node owns the exact
already-landed declarations via an existing record and lean.note. Its module
import provides these definitions; the extension theorem is not used. This
repairs the ownership defect without a second definition or a library refactor.

Additional self-reading by Q46: checked every declaration named in the new
owner against its node text and Stacks 06HR/06HS, including the final arrow
equality for the prescribed identification. The empty-tower case is excluded
by Nat indexing with exponent n+1, the field-completion case is allowed, the
identity surjection is retained, and there is no separability hypothesis or
smaller test universe. No mathematical signature changed from the independently
checked returned version. Independent maintainer review remains required.
