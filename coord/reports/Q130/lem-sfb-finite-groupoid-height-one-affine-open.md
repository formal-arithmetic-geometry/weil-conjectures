## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteGroupoidHeightOneAffineOpen` states
`AlgebraicGeometry.exists_isAffineOpen_invariant_of_orbit_stalk_dimension_le_one`.
The only proof is `sorry`; no definitions or auxiliary theorems are introduced.
The item statement is unchanged. Source checked in the local Stacks text:
`literature/stacks-project/more-groupoids.tex`, lines 2805–2950, Tag 0ABI,
`lemma-find-affine-codimension-1` (including the entire proof).

Hypothesis and conclusion correspondence:

- Schemes `U,R`: `{U R : Scheme.{u}}`, with an arbitrary explicitly declared universe `u`.
- Source, target, identity, inverse, composition: `(s t : R ⟶ U)`, `(e : U ⟶ R)`,
  `(i : R ⟶ R)`, `(c : pullback s t ⟶ R)`.
- Absolute groupoid laws: `_hG : IsGroupoidScheme s t e i c`, exactly the recorded
  dependency, including all test-scheme groupoid laws and naturality through composition.
- Both maps finite: `[IsFinite s] [IsFinite t]`.
- Locally Noetherian: `[IsLocallyNoetherian U]`.
- Separated as a scheme: `[U.IsSeparated]`. Mathlib's protected class
  `Scheme.IsSeparated` in `Morphisms/Separated.lean:338` means separatedness of
  `terminal.from U`. `specULiftZIsTerminal` in `AlgebraicGeometry/Limits.lean:55`
  identifies the terminal scheme with Spec of the universe lift of Z, so this is
  exactly the stated absolute separatedness, with no choice of a field or base.
- Distinguished point: `(u : U)`.
- Orbit: the existing set operations `t '' (s ⁻¹' ({u} : Set U))`. This is exactly
  the set in the node, using all underlying scheme points of R. An arrow's residue
  field already receives the residue fields of both endpoints. No demand that an
  arrow be rational over either endpoint is made. Common residue-field extensions
  needed to compose arrows do not restrict this image set.
- Dimension at every orbit point: `_hdim : ∀ w ∈ t '' (s ⁻¹' ({u} : Set U)),
  ringKrullDim (U.presheaf.stalk w) ≤ 1`. The numeral is in `WithBot ℕ∞`.
- Open subscheme W: `∃ W : U.Opens`. Mathlib's `Scheme.Opens.toScheme` supplies
  its restricted structure sheaf and canonical open immersion.
- Affineness: `IsAffineOpen W`, defined by Mathlib as `IsAffine W`.
- Containment of the whole orbit: `t '' (s ⁻¹' ({u} : Set U)) ⊆ (W : Set U)`.
- Invariance as open subschemes: `s ⁻¹ᵁ W = t ⁻¹ᵁ W` in `R.Opens`; open
  subschemes carry the canonical restricted sheaf, so no extra scheme structure
  or unrecorded scheme-theoretic equality is being assumed.
- The final clause excluding field and finite-type-over-a-field hypotheses is
  respected: neither a field nor such a morphism occurs in the signature.

Statement dependencies read and used:

- `def-a1-groupoid-scheme`: `Sheaf.AlgebraicGeometry.GroupoidScheme`,
  `AlgebraicGeometry.IsGroupoidScheme` (full structure and documentation read).
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite`; the accompanying `IsIntegralHom` signature was
  also inspected, but no integrality assumption is added to this theorem.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsSeparated` (via `Scheme.IsSeparated` from its public
  separatedness dependency). No properness hypothesis is used.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`, through canonical open subschemes.

Every recorded statement-dependency module is a public import. Already recorded
proof-dependency modules are plain imports, including norm charts, the invariant
norm theorem, and the two local-ring comparison modules. Nodes with no recorded
Lean module are not imported. No absent proof prerequisite is needed to state
this theorem. The declaration docstring transcribes all fourteen proof steps
and their dependency IDs from the node, so stage 3 can resume directly.

Edge cases checked before writing: an empty U has no distinguished point and is
therefore excluded only by the node's own `u ∈ U`; R cannot be empty when U is
nonempty because of the identity map. The identity groupoid reduces to an affine
neighborhood of a point of local dimension at most one. Dimension zero is included
by `≤ 1`, with no positive-dimensional assumption. Nonreduced schemes, varying
finite-map degrees, non-quasi-compact locally Noetherian U, mixed characteristic,
and schemes not of finite type over any field are not excluded. No freeness,
flatness, reducedness, orbit cardinality, or global Noetherian hypothesis is added.
A finite orbit is a consequence used in the proof, not an extra hypothesis.

Searches for an existing statement:

- `msearch.py ... leanfinder`: “A finite groupoid scheme with locally Noetherian
  separated object scheme admits an invariant affine open neighborhood of an
  orbit whose points have local dimension at most one”. Eight hits: finite-map
  affine characterization, affine-neighborhood reduction and cover lemmas,
  finite discrete schemes; none gives invariant affine opens for finite groupoids.
- `msearch.py ... loogle`: `AlgebraicGeometry.IsGroupoidScheme,
  AlgebraicGeometry.IsAffineOpen, ringKrullDim`. Zero hits; the first identifier
  is unknown to the Mathlib search service (it is a project declaration).
- `msearch.py ... leansearch`: “finite groupoid invariant affine open neighborhood
  local dimension one”. Eight hits, mostly manifold structure groupoids and one
  affine-space finite-presentation instance; no matching statement.
- `msearch.py ... grep`: `groupoid.*affine|affine.*groupoid|heightOne|height_one`
  in `AlgebraicGeometry`. Three unrelated elliptic-curve height-one-spectrum hits.
- `rg` on the project's `lean/WeilConjectures` and `lean/Sheaf` for height-one,
  groupoid, invariant-affine and codimension-affine names. Found the recorded
  absolute groupoid definition, affine-groupoid norm and invariant-ring theorems,
  and unrelated height-one facts; none states this node. The field/action quotient
  interfaces have additional hypotheses and do not give the absolute theorem.
- Exact blueprint-ID search in `lean/WeilConjectures` and
  `dag/lean_names_upstream.json` found no declaration attached to this node.

No node faults or statement disputes were found. The previously recommended
`Sheaf.CategoryTheory.CompactObject` example is withdrawn; its node now records
`WeilConjectures.CategoryTheory.CompactObject`, whose module header and docstring
conventions were read instead.

## Second reading by Q130

A separate rereading by the same dispatched worker, with the node, final signature
and Stacks Tag 0ABI open, checked each binder and conclusion listed above. This is
not claimed to be an independent-agent review; the dispatch brief prohibits
starting another agent and assigns independent review to the maintainer.

The groupoid predicate uses the dependency's actual absolute interface rather
than the different older `Scheme.IsGroupoid` interface used by a proof dependency.
The two finite hypotheses are both present; absolute separatedness is checked
against `Scheme.IsSeparated` rather than relative separatedness over a field.
The stalk-dimension assumption quantifies over every point in the actual image
orbit. All three conclusion clauses occur as separate conjuncts. Equality is
in the lattice of opens of R, retaining the canonical open-subscheme meaning.
The arbitrary universe is explicitly bound. No mismatch or correction was found.
