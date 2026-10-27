## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceFiniteTypeFppfEffectivity` states
`AlgebraicGeometry.AlgebraicSpace.finiteType_fppf_descent_effective`, with its whole
proof `sorry`. It states the scheme-base specialization of Stacks Tag 0ADV(2),
`bootstrap-lemma-descend-algebraic-space`. I read that statement and its proof,
and Tag 04U0 (`lemma-locally-algebraic-space-finite-type`), in
`literature/stacks-project/bootstrap.tex`. The accepted nine-step DAG proof is
retained verbatim in the node and rendered step by step in the theorem docstring.
No definition, auxiliary theorem, or new node is introduced.

Hypotheses and clauses, matched individually:

- The scheme T is `(T : Scheme.{u})`; the covering schemes are
  `(Tᵢ : I → Scheme.{u})`, and their arrows are `(p : ∀ i : I, Tᵢ i ⟶ T)`.
- The universe convention is explicit `universe u w`; schemes have Mathlib's
  usual object universe u+1 and morphism universe u. The sheaves take values
  in `Type u`, exactly as the recorded `AlgebraicSpace` definition. The index
  is `{I : Type w}`, independently of the scheme universe. There is no
  countability, finiteness, nonemptiness, or smallness hypothesis on I.
- An fppf covering is `hcov : Presieve.ofArrows Tᵢ p ∈ Scheme.fppfPrecoverage T`.
  By its recorded definition this is joint surjectivity and flatness plus local
  finite presentation of every p i. The covering maps need not be quasi-compact.
- The local sheaves and specified gluing data form
  `D : (Scheme.fppfTopology.pseudofunctorOver (Type u)).DescentData p`.
  Here `D.obj i` is a sheaf on `Scheme.fppfTopology.over (Tᵢ i)`.
  `hAlg : ∀ i, IsAlgebraicSpace (D.obj i)` supplies exactly the representable
  diagonal and representable surjective étale atlas of each local space.
- Each local structure morphism is the unique natural transformation
  `((Over.mkIdTerminal.isTerminalObj yoneda _).from (D.obj i).obj)`.
  Its target is `yoneda.obj (Over.mk (𝟙 (Tᵢ i)))`, the presheaf represented
  by the base itself. `Over.mkIdTerminal` is the identity slice object's
  terminality, and Yoneda preserves limits. Thus this term is the canonical
  map to the base, not a chosen map or an extra structure hypothesis.
- `hft i` is the conjunction of `MapIsQuasiCompact` of that structure map
  and `MapToSchemeIsLocally (@LocallyOfFiniteType)` of the same map and
  local algebraic space. The former tests compactness after every affine
  scheme test; the latter tests the actual scheme map on every representable
  étale chart. They impose exactly quasi-compactness and local finite type,
  with no separatedness, finite presentation, or representability assumption.
- For a scheme Y mapping to both Tᵢ i and Tᵢ j over T, `D.hom` compares
  the restrictions of the two local sheaves to Y. On `Y = Tᵢ i ×_T Tᵢ j`
  this is the given φ_ij, after the canonical interpretation of a sheaf on
  a slice as its fibre product over the represented base. `D.pullHom_hom`
  says these comparisons pull back naturally, so it equivalently records
  the same sheaf overlap map on all tests. `D.iso` proves each comparison
  invertible from `hom_self` and `hom_comp`; no independent invertibility
  hypothesis or additional datum is needed.
- `D.hom_self` is the identity after restriction along the diagonal;
  `D.hom_comp` is φ_jk composed with φ_ij equals φ_ik on every triple
  overlap. These fields are the usual descent cocycle, not a stronger
  demand that φ_ii be the identity over the entire self-intersection.
- The conclusion quantifies `∃ X : AlgebraicSpace T`, so it supplies the
  descended algebraic space over T. Its fppf sheaf is `X.obj`.
  `toDescentData p` restricts this sheaf to each Tᵢ i, equivalently its
  sheaf fibre product with that base. The claimed
  `Nonempty (D ≅ (toDescentData p).obj X.obj)` provides the local
  isomorphisms. Their compatibility with the original φ_ij is part of
  `DescentData.Hom.comm` in the isomorphism. Invert the component
  isomorphisms for the direction X ×_T Tᵢ → X_i in the node.
  The conclusion does not add a global finite-type assertion or uniqueness.

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`:
  `AlgebraicGeometry.AlgebraicSpace`, `IsAlgebraicSpace`, `IsRepresentable`,
  `IsRepresentableWith`, `IsEtale`, `IsSurjective`. I read their signatures,
  definitions and docstrings. These are the given sheaf/atlas interface.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `Scheme.Hom` (full structure signatures and docstrings read).
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`; `Mathlib.CategoryTheory.Sites.Over` supplies
  `GrothendieckTopology.over`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; the quasi-compact scheme
  definition recorded by the same dependency is `QuasiCompact` in
  `Morphisms.QuasiCompact`. The algebraic-space versions below are needed
  because the local spaces are not assumed to be schemes.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, whose complete signature and proof
  docstring I read. It supplies the sheaf fibre-product convention and is
  imported publicly. Its other two recorded clauses were also read.
- `def-weil-size-convention` has a convention record, not an object to
  import. Universe binders implement it directly.
- Added landed dependency `def-sfb-proper-curve-moduli`, from
  `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact` and
  `MapToSchemeIsLocally`, whose full definitions and source docstrings
  were read. These are the existing general morphism predicates; none
  of `IsProperCurveFamily`, properness, or a dimension bound is used.
- Mathlib's `GrothendieckTopology.pseudofunctorOver`,
  `Pseudofunctor.DescentData` (all fields), `DescentData.iso`, its morphism
  structure (including `comm`), and `toDescentData` were read in
  `Sites/PseudofunctorSheafOver.lean` and
  `Sites/Descent/DescentData.lean`. `Over.mkIdTerminal` and
  `Limits.IsTerminal.isTerminalObj` supply the actual structural arrow.

All currently recorded proof-dependency modules are imported with plain
`import` when not already public statement imports: SetSheafCoverDescent,
BoundedAffineLocallyFiniteTypeCoproduct, StackChartwiseSmoothEtaleCalculus,
AlgebraicSpaceCoproduct, FppfSheafCoproductPartition, and the Mathlib matches
in Morphisms.UniversallyOpen and AlgebraicGeometry.Limits. The three proof
nodes fppf-space-atlas-bootstrap, qc-space-affine-etale-atlas and
stack-finite-type-calculus have no recorded declarations yet, so have no
module to import. They are proof prerequisites, not missing objects used
in this signature. The supplied proof plan retains them.

Edge cases checked before writing:

- Empty I is permitted. Its covering hypothesis holds exactly for an empty
  base, and the empty algebraic space gives the required effectivity.
- Singleton identity cover gives ordinary restriction to the same base;
  hom_self excludes nontrivial diagonal comparison.
- Repeated cover members are permitted; the datum's maps are indexed by
  their labels and by maps from overlap tests, not by a set of distinct images.
- Empty local spaces and empty overlaps are permitted: no inhabitance of
  section sets or point sets is assumed. In a mixed nonempty cover, the
  datum itself requires consistency on nonempty overlaps, as it should.
- Non-quasi-separated spaces and non-quasi-compact bases are included.
  Finite type only concerns the local maps to their bases. Étale atlases
  are not required to be finite type or quasi-compact as morphisms.
- The index universe w is arbitrary; the size argument must use a bounded
  affine refinement, as in the accepted proof, rather than form the
  unrestricted original scheme coproduct. No countability condition is
  hidden in the statement. The terminal-presheaf structural arrow uses
  hom universe u, consistently with the algebraic-space definition.

Searches for an existing declaration (all on this machine through the
prescribed msearch.py wrapper, plus read-only rg):

- LeanFinder: `Fppf descent data for finite type algebraic spaces are effective`.
  Eight hits on abstract effective epimorphisms and stack descent, including
  `Pseudofunctor.isEquivalence_toDescentData`; none establishes algebraicity
  of the descended sheaf. No exact match. The same query was issued twice
  while retrieving the first command's delayed result.
- Loogle: `AlgebraicGeometry.AlgebraicSpace, DescentData`.
  Zero hits, unknown identifier `AlgebraicGeometry.AlgebraicSpace` in Mathlib.
- Mathlib grep: `AlgebraicSpace|descent.*finite.type|finite.type.*descent`
  under `AlgebraicGeometry`: zero hits.
- LeanSearch: `Effective fppf descent for algebraic spaces of finite type`.
  Eight hits on scheme property descent and algebraic finite-type results,
  including `descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact`.
  No algebraic-space effectivity statement.
- Read-only rg over both `lean/WeilConjectures` and `lean/Sheaf` for
  `lem-sfb-space-finite-type-fppf-effectivity|fppf.*effect|effect.*fppf`,
  and for `finiteType_fppf_descent_effective|finite.type.*descent.*effective`:
  no exact statement. Broader `Descent`, `FiniteType`, and `MapIsQuasiCompact`
  searches found the reused sheaf descent and existing morphism predicates.
- `dag/lean_names_upstream.json` search for the proposed declaration and
  module name: no collision. No private copy of any notion is introduced.

No statement correction, disputed statement, new node, or dependency repair
is needed. The only non-lean item-field change is adding the already landed
owner `def-sfb-proper-curve-moduli` to stmt_deps, as authorized by brief-stage2
§5 (STMT_DEPS MAY GAIN LANDED NODES). The source statement and accepted split
are unchanged. All files were written only inside the assigned sandbox.

Validation: scompile.py compiled the delivered module as a sandbox module
and under its library name, both within the default 60-second limit. The
final header is compiled again before delivery; deliver2.py runs the
server preflight and per-file compiler. Only the intentional theorem sorry
is present.

## Second reading by Q06

I re-read the node, Mathlib descent-data fields, the local finite-type
predicate bodies, and the completed signature. This is a worker self-check;
the independent mathematical reading is the maintainer's delivery review,
as the dispatcher brief specifies, and no other agent was started.

The covering hypothesis is membership in the fppf precoverage, not merely
an arbitrary generated covering sieve. Each local sheaf is over its own Tᵢ,
not over the wrong common base. The local algebraicity predicate and both
finite-type conjuncts are present. The canonical terminal Yoneda arrow
has the intended base and no arbitrary morphism parameter. The descent
cocycle includes diagonal normalization and natural pullback compatibility.
The output is an isomorphism in the descent-data category rather than a
family of unrelated local isomorphisms, so precisely the given comparisons
are recovered. I checked empty and repeated members and the independent
index universe. No mathematical mismatch or silent statement change was
found. The header was adjusted to explicitly import the statement-owner
modules and every available proof-dependency module, including the two
Mathlib matches. No extra hypothesis, conclusion, or construction was added.
