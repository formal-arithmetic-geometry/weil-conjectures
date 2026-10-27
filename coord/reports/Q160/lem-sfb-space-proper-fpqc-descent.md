## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceProperFpqcDescent` states
`AlgebraicGeometry.AlgebraicSpace.proper_iff_fpqc_scheme_cover`, with proof `sorry`.
It introduces no definitions. The item's mathematical statement, proof, and proof
 dependencies are unchanged; only `lean` and two additions to `stmt_deps` are delivered.

Clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| A scheme T | `T : Over S`, with underlying scheme `T.left` |
| An algebraic space X | `X : AlgebraicSpace S` |
| A morphism f : X → T | `f : X ⟶ schemeSpace T` |
| A set-indexed family of schemes T_i → T | `{I : Type v}`, `Tᵢ : I → Over S`, `g : ∀ i : I, Tᵢ i ⟶ T` |
| The family is fpqc | `hg : Presieve.ofArrows (fun i ↦ (Tᵢ i).left) (fun i ↦ (g i).left) ∈ Scheme.fpqcPrecoverage T.left` |
| The fibre product and projection f_i | `enlargedFibreProductFst (ObjectProperty.homMk ⟨yoneda.map (g i)⟩ : schemeSpace (Tᵢ i) ⟶ schemeSpace T) f` |
| f proper iff every f_i proper | `MapIsProper f ↔ ∀ i : I, MapIsProper (...)` |
| Proper means separated, finite type, universally closed | The existing `MapIsProper` is exactly `MapIsSeparated f ∧ MapIsFiniteType f ∧ MapIsUniversallyClosed f`; finite type is the existing quasi-compactness and local finite type chart test |
| No finite presentation, Noetherian, flatness, connectedness, nonemptiness hypotheses on f | None occurs in the signature |

`S : Scheme.{u}` is an unrestricted ambient scheme for the definition of algebraic
spaces over a scheme. It imposes no restriction: any map X → T of the node can use
S = T and the identity structure map of T. Keeping S general also agrees with the
Stacks 03YH convention and the existing fpqc qc/separated descent interface. The
cover members have their induced S-structure. Both u and v are explicitly bound;
the family index universe v is independent of the scheme universe u.

The fibre product is written T_i ×_T X rather than X ×_T T_i. Its actual first
projection therefore has target T_i and is canonically the specified f_i; this
is exactly the factor order used in Stacks 03YH. `enlargedFibreProduct` contains the
actual pullback of the underlying fppf sheaves, with no arbitrary map or choice of
an unrelated space. `schemeSpace` retains the actual Yoneda sheaf. The source
Tags 0422 and 03YH were opened in `literature/stacks-project/spaces-descent.tex`
(lines 1666 and 992); the latest blueprint direct-image stability proof (3) was
also read. The module docstring gives all five steps of the accepted DAG proof,
including both directions of the atlas/compact-point-space compatibility.

Dependency declarations used, read with their docstrings and full signatures:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  with its fppf sheaf, representable diagonal and surjective etale atlas definition.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fpqcPrecoverage`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace`, used by the existing bundled pullback.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicSpace.MapIsProper`, `MapIsSeparated`, `MapIsFiniteType`,
  `MapIsLocally`, and `MapIsUniversallyClosed`; the original definitions are reused.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `AlgebraicSpace.schemeSpace`,
  `schemeSheaf_isAlgebraicSpace`, `enlargedFibreProduct`, `enlargedFibreProductFst`.
  The landed definition nodes `def-trf-scheme-algebraic-space` and
  `def-sfb-space-sheaf-fibre-product` are added to `stmt_deps` as declaration owners.
- Proof import `Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcQCSeparatedDescent`:
  `AlgebraicSpace.quasiCompact_separated_of_fpqc_scheme_cover`.
- Proof import `Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteAffineSubatlas`:
  `AlgebraicSpace.exists_finite_affine_subatlas`, `compactSpace_points_of_surjective`,
  `compactSpace_points_of_scheme_atlas`.
- Proof import `Mathlib.CategoryTheory.Sites.Precoverage`:
  `CategoryTheory.Precoverage.mem_coverings_of_isPullback`, the recorded Mathlib
  match of `lem-galois-fpqc-covering-base-change`. Its stability hypothesis is
  provided by `Scheme.fpqcPrecoverage`.

The remaining proof-only nodes `lem-sfb-space-proper-base-change`,
`lem-sfb-space-lft-smooth-fpqc-locality`, and
`lem-sfb-space-fpqc-descend-universally-closed` have no recorded Lean module;
there is no import for them. They are described in the proof docstring and are
not required to type this stage-2 statement.

Edge cases checked mathematically before writing:

- Empty index set: fpqc coverage forces the target to be empty; a space mapping
  to that target is empty. Properness and the universal quantifier both hold.
- Empty X over arbitrary T: the empty map and all its pullbacks are proper.
- Empty T and redundant empty cover members: permitted; no `Nonempty` instance.
- The singleton identity covering recovers properness of the identity base change.
- A faithfully flat field extension need not be of finite presentation; the fpqc
  hypothesis permits it. No field, characteristic, finiteness or separation
  assumption has been added to the covering members beyond fpqc coverage.
- Nonproper f is allowed. The result is an equivalence and does not assume any
  constituent of properness on f. No flatness of f is inferred from coverage.

Searches for existing statements (all on 2026-10-24):

- `msearch.py ... leanfinder "Properness of a morphism from an algebraic space to a scheme is equivalent to properness of all base changes along an fpqc covering family"`:
  eight hits concerning schemes, including `IsProper.instIsZariskiLocalAtTarget`
  and proper-composition results; no algebraic-space fpqc equivalence.
- `msearch.py ... leansearch "Properness of algebraic spaces is fpqc local on the scheme target"`:
  eight hits, including `IsLocalAtTarget`, `IsProper.instIsZariskiLocalAtTarget`,
  `IsProper.of_valuativeCriterion`, and `UniversallyClosed` Zariski locality;
  all are scheme assertions, not this assertion about algebraic spaces.
- `msearch.py ... loogle "AlgebraicGeometry.IsProper, AlgebraicGeometry.Flat"`:
  zero hits.
- `msearch.py ... grep "IsProper.*[Dd]escend|[Dd]escend.*IsProper|AlgebraicSpace"`:
  zero Mathlib hits. Read `Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`:
  `IsProper` is a predicate on scheme maps, so it cannot replace `MapIsProper`.
- `rg -n "MapIsProper|proper_iff.*fpqc|fpqc.*proper" lean/WeilConjectures lean/Sheaf`:
  no upstream match; project definitions and applications were inspected.
  `flat_proper_fp_locality` includes fppf locality, which does not state locality
  for the arbitrary fpqc covering of this item. Strict-local testing and
  properness from connected fibres likewise do not state this equivalence.
- `grep -rn "lem-sfb-space-proper-fpqc-descent" lean/WeilConjectures`: no hits.
- Declaration name `proper_iff_fpqc_scheme_cover` was searched in both project
  roots: no prior declaration. `dag/lean_names_upstream.json` supplied no match.
- Scheme-space and pullback ownership searches in `dag/nodes` found the two
  already landed definition nodes named above; no new node is needed.

No STATEMENT-DISPUTED flag or mathematical node fault was found. The prescribed
example `CompactObject.lean` is now a withdrawn declaration-free module; its node
now records Mathlib's compact-object definition. The current module conventions
were therefore taken from the live dependency modules and the standing brief.

Validation: `scompile.py Q160 lem-sfb-space-proper-fpqc-descent <module path>`
compiled both sandbox and library forms cleanly (1.7 s and 1.6 s). The only
postponed proof is the item's named theorem.

## Second reading by Q160

This is a separate self-reading after compilation, not an independent-agent
review: the dispatcher explicitly forbids starting other agents, and the
maintainer's independent review remains the delivery review. I reopened the node
and the final module and checked every row of the correspondence table. The
source of the pulled-back arrow is the sheaf pullback with the covering scheme
first, and its target is that covering scheme, not X. The fpqc predicate is on
the underlying scheme family, not on algebraic-space atlases or on f. The proper
predicate is the exact recorded three-property conjunction, with no change of
quasi-compactness convention. The two directions are both present in `↔`, and
there is no restriction to fppf covers. The explicit universes and empty-family
case are preserved. No mismatch required a Lean change on this second reading.
The only metadata adjustment was to cite the existing owners of `schemeSpace`
and the bundled sheaf fibre-product construction.
