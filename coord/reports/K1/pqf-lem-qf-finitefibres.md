## Worker report

The module states `AlgebraicGeometry.Scheme.Hom.isQuasiFinite_iff_finiteFibres`, with only
`sorry` as its proof. The node is unchanged except for `lean`. Its `stmt_deps` is empty.
The already landed definitions carried by proof dependency `pqf-def-quasifinite` are
reused directly; no missing notion, new node, or dependency module is needed.

Clause matching:
- “Let f : X → S be a morphism of schemes”: `{X S : AlgebraicGeometry.Scheme.{u}}`
  and `(f : X ⟶ S)`, with the universe explicitly declared and no extra assumptions.
- “quasi-finite if and only if”: `IsQuasiFinite f ↔ ...` using the project's Stacks notion.
- “locally of finite type”: the first `AlgebraicGeometry.LocallyOfFiniteType f` conjunct.
- “of finite type”: the grouped conjunct
  `(AlgebraicGeometry.LocallyOfFiniteType f ∧ AlgebraicGeometry.QuasiCompact f)`.
  Mathlib's FiniteType module defines scheme finite type by these two conditions and
  provides no separate finite-type class. This is also the project's convention.
- “quasi-compact”: the following `AlgebraicGeometry.QuasiCompact f` conjunct.
- “has finite fibres”: `HasFiniteFibres f`, defined as `∀ s : S, (f ⁻¹' {s}).Finite`.

Declarations read and used:
- `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsQuasiFinite` (local finite type, quasi-compactness,
  and each singleton open in its scheme fibre) and
  `AlgebraicGeometry.Scheme.Hom.HasFiniteFibres` (finite set-theoretic fibres).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; its full signature and docstring were read.
- `AlgebraicGeometry.QuasiCompact`, the existing predicate also used by IsQuasiFinite.

Source checked: https://stacks.math.columbia.edu/tag/02NH, Lemma 29.21.10.
It states locally finite type, quasi-compact and finite fibres; the node also spells
out finite type, which is already their conjunction. Keeping that redundant clause
is faithful and does not change the logical strength. The theorem docstring records
both node proof steps and every proof dependency used in them.

Edge cases checked before writing:
- Empty source: all fibres are empty, isolation vacuous, and finite type/quasi-compact
  hold; both sides agree. Empty target forces empty source; both sides agree again.
- Arbitrary identity morphism: singleton fibres and finite type, hence both sides hold.
- Infinite discrete disjoint union of points over a field: local finite type alone
  does not suffice; quasi-compactness and finite fibres fail, as does quasi-finiteness.
- Positive-dimensional finite-type schemes over a field do not have finite fibres;
  the theorem adds no dimension, field, separatedness, or Noetherian assumption.
- Nonreduced finite fibres are allowed: finiteness counts points, not scheme length.
- Arbitrary `u` is allowed and explicitly bound; no restriction on characteristic.

Searches made:
- leanfinder via msearch.py: “A morphism of schemes is quasi-finite if and only if
  locally of finite type of finite type quasi-compact with finite fibres”: eight hits,
  including LocallyQuasiFinite, LocallyOfFiniteType and IsFinite; no exact statement.
- loogle via msearch.py: `AlgebraicGeometry.LocallyQuasiFinite,
  AlgebraicGeometry.LocallyOfFiniteType`: nine hits, including
  `locallyQuasiFinite_iff_finite_preimage_singleton`. Read its signature: it assumes
  local finite type and quasi-compactness and characterizes Mathlib LocallyQuasiFinite,
  not the project's unconditional IsQuasiFinite equivalence. Thus not an exact match.
- grep via msearch.py: `finite_preimage_singleton|class QuasiFinite|isQuasiFinite_iff`
  in AlgebraicGeometry: nine hits, finite-fibre criteria but no exact statement.
- rg on source WeilConjectures for quasi-finite and finite-fibre declarations, and
  the exact node id: existing component results only; no declaration for this node.
- rg on project lean/Sheaf for `finitefibres|HasFiniteFibres|isQuasiFinite_iff`:
  only the finite-fibres definition; related quasi-finite modules were read/searched.

No statement dispute or correction is needed. The node's empty statement-dependency
list omits its existing defining notions; this is reported without modifying that
list, since additions of existing nodes are outside the authorized non-correction fields.

## Second reading by K1

I independently read the node statement, its Stacks source (Tag 02NH, Lemma 29.21.10),
its dependency declaration `AlgebraicGeometry.Scheme.Hom.IsQuasiFinite` and
`HasFiniteFibres` in `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`, and the delivered
file `Sheaf/AlgebraicGeometry/QuasiFiniteIffFiniteFibres.lean`.

The node introduces a morphism of schemes `f : X → S`. The Lean binders
`{X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)` render exactly those objects,
with one common arbitrary universe and no field, separatedness, Noetherian, or
characteristic assumptions. Its conclusion is the equivalence
`IsQuasiFinite f ↔ ...`. The right side is, in order, (1)
`AlgebraicGeometry.LocallyOfFiniteType f`, rendering locally of finite type; (2)
the parenthesized conjunction
`AlgebraicGeometry.LocallyOfFiniteType f ∧ AlgebraicGeometry.QuasiCompact f`,
rendering of finite type under the project's convention; (3)
`AlgebraicGeometry.QuasiCompact f`, rendering quasi-compact; and (4)
`HasFiniteFibres f`, rendering finite set-theoretic fibres. Thus every clause is
present, in the node's order, including its deliberately redundant finite-type
expansion, and no hypothesis or conclusion was added, dropped, strengthened, or
weakened. The declaration's statement in the node copy is verbatim the theorem
signature in the file.

I checked edge cases against the definitions: empty source or target and empty
fibres make the finite-fibre quantifier vacuous where appropriate; identity maps
have singleton fibres; zero-dimensional and nonreduced schemes are not excluded;
no characteristic or positivity assumption appears; and the explicit universe
`u` does not exclude any scheme case covered by the node. The source assumes no
additional hypotheses throughout, matching the Lean statement.

Searches were repeated with `msearch.py`: LeanFinder for a quasi-finite/finite
fibre equivalence (hits only general predicates), Loogle for
`AlgebraicGeometry.LocallyQuasiFinite` and `LocallyOfFiniteType` (the result
`locallyQuasiFinite_iff_finite_preimage_singleton` has different predicates and
hypotheses), and grep for `finite_preimage_singleton|class QuasiFinite|isQuasiFinite_iff`
in Mathlib. `rg` searches of `WeilConjectures/` and the repository's `lean/Sheaf/`
found no exact theorem; the only project definitions are the recorded
`IsQuasiFinite` and `HasFiniteFibres`. Therefore this is not an existing
Mathlib/source declaration and the delivered module is required.

No mismatch was found. I changed no statement, dependency, or definition; the
only addition is this independent second-reading record. The module compiles
cleanly with `scompile.py`, with only the intentional `sorry` proof.
