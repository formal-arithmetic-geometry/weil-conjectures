## Worker report

The module `Sheaf.AlgebraicGeometry.AmpleFibreSectionLifting` states
`AlgebraicGeometry.Scheme.Modules.exists_lift_section_of_fiber_isAmple`.
Its only theorem has proof `sorry`. No definition, axiom, or extra theorem is introduced.
The statement is the final surjectivity assertion of Stacks Tag 0D2M,
`coherent.tex`, `lemma-ample-on-fibre`, with the coherent module equal to O_Z,
expressed using representatives of direct-image stalk elements on neighbourhoods.
I read that source assertion and the node's complete eight-step proof.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes Z and S and their morphism: `{Z S : Scheme.{u}} (f : Z ⟶ S)`.
  The universe u is explicitly bound, and auto-implicit binders are disabled.
- Properness: `[IsProper f]`, Mathlib's separated, universally closed,
  locally finite type definition (universally closed also gives quasi-compactness).
- S Noetherian: exactly `[IsLocallyNoetherian S] [CompactSpace S]`.
- The invertible O_Z-module: `(L : Z.Modules) [L.IsInvertible]`.
- The base point: `(s : S)`.
- Z_s is the scheme-theoretic fibre: `f.fiber s`; the map to Z is `f.fiberι s`.
  Mathlib defines these as the pullback against `S.fromSpecResidueField s`
  and its first projection.
- L_s is the actual tensor pullback: `(tensorPullback (f.fiberι s)).obj L`.
- Fibre ampleness is `hL : @IsAmple (f.fiber s) ...`.
  Its explicit final argument is `((invertible_pullback_tensor (f.fiberι s)).1 L).2`.
  This is an already proved invertibility witness, not an additional assumption.
- The nonnegative integer threshold is `∃ d₀ : ℕ` and all exponents above it
  are `∀ d : ℕ, d₀ ≤ d →`. Since every integer at least a nonnegative
  integer is uniquely a natural number, this covers exactly the stated exponents.
- The arbitrary prescribed fibre section is
  `∀ t : Γ(((tensorPullback (f.fiberι s)).obj L).tensorPow d, ⊤)`.
  `tensorPow` is the recorded recursion, with O at degree zero.
- Its open neighbourhood is `∃ (U : S.Opens) (hs : s ∈ U)`.
  These existential binders follow d and t, so U may depend on both.
- Its lifted section is `t' : Γ(L.tensorPow d, f ⁻¹ᵁ U)`.
  Evaluating on the inverse-image open is precisely sections of the restricted module.
- Equality of its canonical pullback with t is the final equation. First
  `tensorPullbackSection (f.fiberι s) (L.tensorPow d) (f ⁻¹ᵁ U) t'`
  is the actual section 1 tensor t'. The module restriction `.val.map (homOfLE ...).op`
  restricts this to the entire fibre. The containment proof uses only hs and
  `(f.fiberHomeo s x).property`, the identity f(fibre-inclusion(x)) = s;
  it adds no condition. `Eq.mpr (congrArg (fun y : S ↦ y ∈ U) ...) hs`
  transports only that membership proposition, avoiding dependent transport of
  the fibre itself. Finally `(boundaryPullbackPowIso (f.fiberι s) L d).hom.app ⊤`
  maps from pullback of L^d to the dth tensor power of L_s, and the equation is `= t`.

Dependency declarations actually used for the signature (full namespace for the
module-level names below is `AlgebraicGeometry.Scheme.Modules`, except where indicated):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `IsInvertible`, `tensorPow`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: `tensorPullbackSection`,
  `tensorPullbackSectionAdjunction`, publicly importing the actual tensorPullback
  construction from `WeilConjectures.AlgebraicGeometry.TensorPullback`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`, `fiberHomeo`.
- `WeilConjectures.AlgebraicGeometry.Ample`: `IsAmple`.
- `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`:
  `invertible_pullback_tensor`.
- `WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`:
  `boundaryPullbackPowIso`. This is a real recursively constructed isomorphism:
  degree zero is the unit comparison; successor degree is the tensor comparison
  followed by the previous degree. Its tensor comparison transports Mathlib's
  monoidal pullback along the adjunction comparison, rather than choosing an
  arbitrary tensor isomorphism. It agrees with the canonical tensor comparison
  in the recorded invertible-pullback theorem. The chosen normalized adjunction
  in its source and `tensorPullbackSectionAdjunction` have the same unit 1 tensor m.
  This comparison takes any scheme morphism and any module; no immersion or
  square-zero assumption is introduced by its reuse.

The comparison definitions now have a definition owner,
`def-sc-tensor-pullback-power-comparison`, supplied by this repair with `existing: true`.
The item cites that node in place of the mistakenly added theorem dependency
`lem-sc-square-zero-ideal-tensor-unit`. The theorem does not own these plain definitions.
Only the lean record and this dependency addition differ from current main;
the mathematical statement and the Lean module are unchanged.

All stated proof dependencies are imported, with proof-only imports non-public:
SpecLocalRingCanonicalMorphism, CoherentFiniteTypeLocallyNoetherian,
CoherentKernelCokernelLocallyNoetherian, ClosedImmersionCoherentEquivalence,
GradedSerreVanishing, PQFCohomology, Cohomology.Affine.AffineMorphism,
Sheaf.Paper.MLCohomologyPowersIdeal, FormalFunctionsLocalDictionary,
FormalFibreCohomology, and Topology.PresheafModuleStalkFunctor, as well as the
Mathlib modules recorded for the properness/permanence, affine qcqs,
Noetherian ring, and finite-type/Noetherian leaves. The theorem docstring gives
all eight node proof steps, their inputs, and the uniformity argument.

Edge cases checked before writing:

- Empty fibre: the global section module has only its zero section; the zero
  section on f^{-1}S supplies a lift. No nonemptiness condition is imposed.
- Empty Z and empty S: empty Z is covered as above; for empty S there is no s,
  exactly as in the source's point-indexed assertion.
- d = 0 is included when d₀ = 0; both tensor powers are the structure module and
  the comparison is the canonical unit comparison. The theorem does not assert
  that the threshold must be zero.
- A field local ring (m = 0), Artinian bases, zero sections, arbitrary characteristic,
  and non-flat proper maps require no extra binders. The proof follows image
  stabilization, not a flat base-change assertion.
- The quantifier ordering supplies one bound before all d and t, with independent
  choices of neighbourhood and lift afterwards. No affine-neighbourhood,
  flatness, very-ampleness, or common-neighbourhood condition has been inserted.

Searches for an existing statement:

- msearch.py leanfinder: “Sections of sufficiently high powers of an ample line
  bundle on one fibre of a proper morphism over a Noetherian base lift to a
  neighbourhood of that fibre”. OK, 8 hits: structure-sheaf localization and
  spreading-out results such as exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated,
  exists_of_res_zero_of_qcqs_of_top, and exists_lift_of_germInjective_aux. None
  asserts fibre ampleness and high-power section lifting.
- msearch.py loogle: `"IsAmple", "IsProper"`. OK, 0 hits.
- msearch.py grep: `ample.*fibre|fibre.*ample|exists.*lift.*section`,
  Mathlib/AlgebraicGeometry. OK, 0 hits.
- msearch.py leansearch: “For a proper morphism over a Noetherian scheme, sections
  of high powers of a fibre-ample invertible sheaf lift to a neighbourhood”.
  OK, 8 hits: IsProper and its consequences, spreading-out and open-immersion
  map formulas. No exact statement.
- rg in lean/WeilConjectures and lean/Sheaf for fibre/ample combinations and the
  item id finds the parent NoetherianFibreAmpleNeighbourhood, which invokes this
  result in its proof, plus unrelated ampleness criteria. No declaration of it.
  Searching the final declaration name also in dag/lean_names_upstream.json
  finds no collision.
- rg for tensorPow/pullback comparisons finds the existing boundaryPullbackPowIso;
  reading its owning DAG node and full definition confirms it is the canonical
  recursive comparison for arbitrary morphisms. It is reused without any copy.
- The supplied CompactObject example in lean/Sheaf is withdrawn; its node points
  to WeilConjectures.CategoryTheory.CompactObject, which I read for the conventions.
  There is no repair note for this item.

Validation: scompile.py compiled the final module both as an isolated sandbox
module (7.4 s) and at its intended library name (5.1 s), with no errors or
unexpected warnings. An initial dependent-transport elaboration error was fixed
by transporting only the membership proposition, as described above.
No STATEMENT-DISPUTED issue or statement correction is needed.

## Second reading by Q32

This is an author self-audit, not an independent-agent review: the dispatcher
explicitly prohibits starting other agents and assigns the independent delivery
review to the maintainer. Reading the node and the final signature together,
I checked properness, both Noetherian components, invertibility, the actual fibre
and tensor pullback, and fibre ampleness against their recorded definitions.
I then checked the single bound, every sufficiently large nonnegative exponent,
every prescribed fibre section, a point-containing base open, and its section
on the inverse-image open. The final equation uses fixed canonical section and
tensor-power maps, and the containment proof is obtained from membership hs;
it does not assume any extra restriction on U or on f. No hypothesis or conclusion
mismatch was found. The sole compile repair altered only the expression of that
containment proof. No mathematical change was made.

## New nodes

`def-sc-tensor-pullback-power-comparison` registers the three existing definitions in
`WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`:
`AlgebraicGeometry.Scheme.Modules.boundaryPullbackComparison`,
`AlgebraicGeometry.Scheme.Modules.boundaryPullbackTensorIso`, and
`AlgebraicGeometry.Scheme.Modules.boundaryPullbackPowIso`.
Its record is `existing: true`; no new module is supplied and no definition is copied or moved.
I read both local and live-server source using scompile.py --source, and Stacks 01CD
(modules.tex, lemma-tensor-product-pullback) and 0096
(sheaves.tex, lemma-adjoint-pullback-pushforward-modules).

Clause correspondence: arbitrary schemes and j are `{X Z : Scheme.{u}} (j : Z ⟶ X)`.
The fixed adjunction comparison is `boundaryPullbackComparison j`, constructed by
`leftAdjointUniq` from the normalized adjunction and `pullbackPushforwardAdjunction`.
The binary tensor comparison is `boundaryPullbackTensorIso j A B`: its three factors
are exactly theta at A tensor B, inverse `Functor.Monoidal.μIso`, and the tensor
of the inverse theta components. The tensor-power comparison is
`boundaryPullbackPowIso j L d`. Its recursive clauses are theta followed by
`pullbackObjUnitIso j` at zero, and `boundaryPullbackTensorIso` followed by identity
tensored with the previous power comparison at successor. No invertibility or
closed-immersion assumption occurs. The source tensor powers are the actual
`tensorPow` recursion in Modules.Invertible, also read in full at its definition.
Edge cases: d=0 uses the unit, d=1 uses the same recursion, zero modules and empty
schemes are admitted, and arbitrary noninvertible modules and non-immersion maps
remain in the domain of every definition.

New-node searches (raw wrapper results are stored verbatim in its mathlib_searches):
LeanSearch on pullback of tensor powers, 8 hits (ordinary pullback and free-sheaf
comparisons, no explicit tensor-pullback power construction); LeanFinder on canonical
tensor-pullback comparisons, 8 hits (ordinary TensorPower, polynomial laws and presheaf
tensor products, no exact comparison); Loogle on leftAdjointUniq and Monoidal.μIso,
0 hits; Mathlib grep on the three names and tensorPow in AlgebraicGeometry, 0 hits.
Project grep finds the existing three definitions and their consumers; scanning all
DAG definition nodes' lean records finds no owner. The blueprint_refs search
`tensor.*pullback|pullback.*tensor` returns 0 blueprint matches. The ancestor query
confirms `lem-trf-local-term-locality`; the new node prepends this item to its via list.

## Repair of return H2

The return at immutable head e19deccb3b30 requires definition ownership for the plain
comparison constructions, rather than a dependency on the square-zero unit theorem.
That repair is made above. The saved packet's initial dry run passed at b174c117269;
passing mechanics did not resolve the review point. Comparison with current main
showed only the expected lean record and extra dependency, so the retained statement,
proof plan and Lean source were preserved. There is no statement correction and no
new theorem, axiom or postponed proof. The existing source docstrings are retained.

Second reading of this repair by Q32: I checked each of the three definition bodies
against the new node, including orientation of the tensor comparison, the zero-power
unit and the successor recursion. I checked that the item refers to the new definition
node and no longer to the square-zero theorem. The original hypothesis-by-hypothesis
and clause-by-clause audit above remains valid because the Lean file is unchanged.

Repair validation: scompile.py checked the retained theorem module at both sandbox
and intended library names with no errors or unexpected warnings (7.4 s and 5.1 s).
The repaired-packet dry run compiled both the existing-definition probe and the
item, then required `lean.branch: slopmaster2` for the existing WeilConjectures
module; that metadata was corrected. Self-check also verified both recorded
signatures verbatim, the item's only changed fields against current main,
all new-node cited definitions, line widths, and the sole expected theorem sorry.
