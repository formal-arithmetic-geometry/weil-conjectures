## Worker report

This repairs returned head `0627dcbfe947`. The retained packet was inspected and its initial
`deliver2.py --no-push` passed mechanically at `e328990f5f`; it still had the five mathematical
faults in the return, all repaired below. The current shared node was read alongside the
packet and the Stacks source. The delivery retains the original natural-language statement,
source, proof, proof dependencies and other metadata. No statement correction remains.
The only DAG changes are `lean` and the addition of the published prerequisite
`lem-weil-pbc-fs-adic-completion-map-local` to `stmt_deps` for the canonical completion map.

The module states `AlgebraicGeometry.formalLocalStructureNodalFamily`, with `sorry` as its
only theorem proof. Its helper definitions are constructions belonging to this same local
model, all listed in `lean.declarations`; each has its source and blueprint docstring.
All rings, schemes, completions and power series use the dependency interfaces and Mathlib,
not replacement structures. `@AlgEquiv` is the fully explicit form of `≃ₐ[R]`, used to supply
the canonical algebra structures without installing competing global instances or using
file-local instances/notation or `let` binders in the theorem statement.

Each hypothesis and clause of the prose statement is rendered as follows:

- Schemes `T,S`, the morphism and point: `X Y : Scheme.{u}`, `f : X ⟶ Y`, `t : X`.
  The image `s` is `f t`; the corresponding fibre point is `f.asFiber t`. This already
  matches the original prose's ambient point, so it requires no `statement_change`.
- Flatness at `t`: `hflat : (f.stalkMap t).hom.Flat`, the stalkwise condition of
  `AlgebraicGeometry.Flat.iff_flat_stalkMap`.
- Noetherian base local ring: `[IsNoetherianRing (Y.presheaf.stalk (f t))]`.
- Local finite type: `[LocallyOfFiniteType f]`.
- Closed point of the fibre: `ht : f.asFiber t ∈ closedPoints (f.fiber (f t))`.
- Equality of residue fields through the induced map:
  `hκ : Function.Bijective (f.residueFieldMap t).hom`. This is the actual map
  `κ(s) → κ(t)`, not an unrelated abstract field equivalence.
- The split-node completed fibre algebra: `hspecial` is `Nonempty (@AlgEquiv κ(s) ... ...)`,
  from the completed fibre stalk to `formalNodalPowerSeriesQuotient κ(s) 0`.
  `formalNodalFiberCompletionAlgebra` uses the canonical fibre projection, the canonical
  constants-to-stalk map of `Spec κ(s)`, and completion. The quotient is
  `κ(s)[[u,v]]/(uv-C(0)) = κ(s)[[u,v]]/(uv)`, and its coefficient action is Mathlib's.
- The parameter: `∃ h : formalNodalCompletedStalk Y (f t)`, with membership in
  `Ideal.map (algebraMap A Â) (IsLocalRing.maximalIdeal A)`. Thus `h ∈ m_A Â`.
- The formal equation: `Nonempty (@AlgEquiv Â ... ...)` with target
  `formalNodalPowerSeriesQuotient Â h = Â[[u,v]]/(uv-h)` and source `Ô_{T,t}`.
  The source action is `formalNodalCompletedStalkAlgebra f t`, and the target action is
  the canonical coefficient action through power series and quotient. This is an
  isomorphism of `Â`-algebras, not merely a ring isomorphism.
- Every stalk completion in the signature is `formalNodalCompletedStalk`, which unfolds
  to `AdicCompletion (IsLocalRing.maximalIdeal stalk) stalk`.
- The equivalent model is exactly `formalNodalModel Â h`, defined as
  `Spec (CommRingCat.of (formalNodalModelRing Â h))`, whose coordinate ring is
  `MvPolynomial (Fin 2) Â ⧸ Ideal.span {X 0 * X 1 - C h}`.
- Its origin is `∃ o : formalNodalModel Â h` with
  `o.asIdeal = formalNodalOriginIdeal A h`. That ideal is the image in the quotient of
  `Ideal.map C (m_A Â) ⊔ Ideal.span {X 0, X 1}`: precisely `(m_A Â,u,v)`.
  The prime-spectrum point supplies primality, while the equality fixes the point.
- The completed-model isomorphism is the second `Nonempty (@AlgEquiv Â ... ...)`,
  from `Ô_{T,t}` to `formalNodalCompletedStalk (formalNodalModel Â h) o`.
  `formalNodalModelCompletionAlgebra` gives its canonical `Â`-action through the polynomial
  quotient, the affine constants-to-stalk map, and maximal-ideal completion.
- Its residue field is the actual scheme residue field at that same `o`, with
  `Nonempty ((formalNodalModel Â h).residueField o ≃+* A ⧸ maximalIdeal A)`.

The completed stalk scalar map is not arbitrary data chosen from `Nonempty`.
It uses `RingHom.exists_adicCompletion_map_of_local` in the published module
`Sheaf.RingTheory.CompletionMapForLocalHom`. Its property fixes every finite quotient
coordinate. Given two witnesses, choose a representative of each source coordinate;
the property gives equal target coordinates for all `n`, hence `AdicCompletion.ext_evalₐ`
gives equality. Thus the theorem determines exactly the canonical completed local map,
which is permitted by the project's construction rule. The theorem's proof was read;
it constructs the coordinate maps and applies `AdicCompletion.liftRingHom`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, `Flat.iff_flat_stalkMap`;
  the local hypothesis uses `RingHom.Flat` rather than requiring global flatness.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`, `asFiber`.
- `Mathlib.Topology.JacobsonSpace`: `closedPoints` (the dependency is a Mathlib leaf).
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  its ring and coefficient algebra structures.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `X`, `C`.
- `Sheaf.RingTheory.CompletionMapForLocalHom`: `RingHom.exists_adicCompletion_map_of_local`,
  added as the existing published prerequisite mentioned above.
- Supporting canonical constructions: `StructureSheaf.toStalk` from the scheme API,
  `MvPolynomial`, `Ideal.map`, `Ideal.span`, and ideal quotients from Mathlib.

The stated proof-dependency modules are imported without `public`, preserving all fourteen
DAG steps as the stage-3 proof plan. The theorem docstring reproduces all fourteen complete
proof steps, including their exact dependency identifiers, not a short proof summary.

Edge cases checked against the actual signature: empty schemes have no `t`; the zero ring
cannot be a scheme stalk at a point; `A` a field allows `h=0`; the family `uv=a` over a
one-parameter complete base gives the expected parameter and coefficient action. Zero and
nilpotent `h`, mixed characteristic and characteristic two are included. No global
Noetherianity or global flatness is assumed. The model origin remains defined by the same
ideal when `h=0` or is nilpotent. All scheme and ring objects use the common arbitrary
universe `u`, with no imposed extra universe equality. Every variable is explicitly bound.
There are no unresolved statement disputes.

Searches retained from the original packet: `msearch.py leanfinder`/`leansearch` for formal
local nodal equations and flat deformations; `loogle` for `MvPowerSeries`, `AdicCompletion`,
fibres and stalk maps; grep of Mathlib AlgebraicGeometry/RingTheory; and `rg` over
`WeilConjectures` and `lean/Sheaf`. They locate the underlying constructions, but no theorem
with this complete statement. The node's existing detailed search records are unchanged.
Refreshed searches in this repair:

- `msearch.py leanfinder "A flat family at a split node has completed local algebra A formal
  power series in two variables modulo uv minus h"`: eight hits, smooth-flat and
  Weierstrass preparation interfaces; no matching nodal-family theorem.
- `msearch.py loogle "AdicCompletion, AlgEquiv, Scheme.Hom.stalkMap"`: no hits;
  the service does not recognize the abbreviated scheme identifier.
- `rg "formalNodal|formalLocalStructureNodalFamily|lem-trf-formal-local-structure-nodal-family"`
  in the permitted upstream/project source and DAG directories: only the original node,
  its citer and the citer's proof docstring; no duplicate definition or theorem.
- `rg "liftRingHom|IsLocalHom.*AdicCompletion|AdicCompletion.*IsLocalHom|def .*ompletion"`
  in `lean/Sheaf/RingTheory` and `lean/Sheaf/AlgebraicGeometry`: found the published
  `CompletionMapForLocalHom` interface, which is reused. Other private completion maps
  need not be copied or replaced.

## Return repairs

F1: Both conclusions now use `AlgEquiv` over `Â` with canonical structure maps.
F2: The model is the actual polynomial quotient spectrum; `o` has the prescribed ideal,
its completed stalk is isomorphic to the total-space completed stalk as an `Â`-algebra,
and its actual residue field is compared to `A/m_A`.
F3: `hspecial` is a `κ(s)`-algebra equivalence. Equivalence witnesses carry no redundant
`Function.Bijective` conjunct; `hκ` retains bijectivity because it concerns a ring map.
F4: The original prose statement is restored byte-for-byte, and `statement_change` removed.
The original statement already quantified `t ∈ T`; the previous reason was incorrect.
F5: The docstring contains all fourteen full proof steps and the named dependencies.

## Self-check by Q23

I read the prose statement, the original source paragraphs (0CBX and the first proof of
0CBY), the repaired signature and every helper side by side. In particular the first and
second conclusion `AlgEquiv` instances share the same canonical completed stalk action;
the model action is the canonical coefficient action. The origin belongs to `M_h`, not to
`Spec A`, and its ideal equality constrains its identity. `hspecial` uses the canonical
residue-field action. The only theorem is the assigned theorem, with a `sorry` proof;
helper definitions contain real data and no `sorry`. All fourteen proof steps are present.
This is the worker's self-check; the maintainer supplies the independent review.

Citer checked: `lem-trf-nodal-family-etale-local-model`, proof steps 4 and 5. It requires
the completed split-node equation as an `Â`-algebra and its equivalent origin model for
relative approximation. Both now match the original node and that use. The earlier
`holds:true` for the weaker ring-only packet was incorrect; the repaired statement
supplies precisely the required algebra equivalences. No citer was edited.

## Validation

`scompile.py Q23 lem-trf-formal-local-structure-nodal-family
lean/Sheaf/TraceFormula/FormalLocalStructureNodalFamily.lean` passed for the final module,
including the proof imports: sandbox compile 42.4 s, library compile 3.6 s, no warnings
or errors. Source self-check: fourteen numbered proof steps, one `sorry`, no lines over
100 columns, every helper in `lean.declarations`, and `lean.statement` is the exact
signature. The restored statement is byte-identical to the current shared prose;
only `lean` and the one added prerequisite differ in the node.

`deliver2.py Q23 lem-trf-formal-local-structure-nodal-family --no-push` passed server
preflight and compilation at dry-run commit `3ee5dd1b71`. After that dry run the report's
citer-step reference was corrected from 4/6 to 4/5 and this validation note was added;
the Lean source and node were unchanged. The final delivery wrapper repeats its gates.

## Second reading by Q23

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
