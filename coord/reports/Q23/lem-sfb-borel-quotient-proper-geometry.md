## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.BorelQuotientProperGeometry` states
`AlgebraicGeometry.homogeneousQuotient_geometry`, with its sole proof `sorry`.
It strengthens the geometry of the GIVEN quotient, rather than asserting the
existence of another quotient or assuming the geometric conclusions. No definitions
or auxiliary theorems are introduced. The module docstring and theorem docstring cite
Milne, Corollaries 5.26--5.27 (p.105), Proposition 7.15 (pp.142--143), Theorem 17.9(a)
(p.354), and the Stacks inputs in the node. The theorem docstring records all seven
proof steps and their dependencies.

Hypothesis and clause correspondence:

- Algebraically closed field F: `{F : Type u} [Field F] [IsAlgClosed F]`.
- F-group schemes G and H: `(G H : Over (Spec (.of F))) [GrpObj G] [GrpObj H]`.
  An Over morphism is a morphism over F; thus both the subgroup inclusion and
  quotient map have the specified base compatibility, not arbitrary scheme maps.
- G is affine: `[IsAffine G.left]`.
- G is smooth: `[Smooth G.hom]`.
- G is connected: `[ConnectedSpace G.left]`, including nonemptiness.
- G is finite type: `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`.
- H is a closed subgroup: `(i : H ⟶ G) [IsClosedSubgroupScheme i]`.
  The recorded class includes the homomorphism condition and closed immersion.
- H is smooth and connected: `[Smooth H.hom] [ConnectedSpace H.left]`.
  Affineness and finite type of H are consequences of its closed embedding into G,
  not additional hypotheses.
- The specified F-scheme and quotient map: `(X : Over (Spec (.of F))) (p : G ⟶ X)`.
- Faithful flatness: `[Flat p.left] [Surjective p.left]`.
- Finite presentation: `[LocallyOfFinitePresentation p.left] [QuasiCompact p.left]
  [QuasiSeparated p.left]`, precisely the quotient dependency's convention.
- Equality of images on EVERY F-test scheme iff the ratio is in H: `hcoset`,
  quantifying `(T : Over (Spec (.of F))) (a b : T ⟶ G)`, with
  `a ≫ p = b ≫ p ↔ a⁻¹ * b ∈ Set.range (fun h : T ⟶ H ↦ h ≫ i)`.
- Fpqc local lifts of EVERY point on EVERY test scheme: `hlift`, quantifying
  `T` and `x : T ⟶ X`, an index type `I : Type u`, test schemes `T'`, arrows `f`,
  membership of their underlying presieve in `Scheme.fpqcPrecoverage T.left`, and
  for each index a lift `g` satisfying `g ≫ p = f j ≫ x`. This is verbatim the
  local-lifting clause of the recorded homogeneous quotient declaration.
- Smooth G and X: `Smooth G.hom` and `Smooth X.hom` in the conclusion. Smoothness
  of G is deliberately repeated because the node explicitly includes both schemes
  in its conclusion; the node's redundant clause is preserved.
- Geometrically integral G and X: `GeometricallyIntegral G.hom` and
  `GeometricallyIntegral X.hom`. Mathlib defines this by integral pullbacks along
  every `Spec K → Spec F`. Such a morphism is a field embedding F → K, exactly
  a field extension. This is not a condition merely on algebraic or closed fields.
- Regular G and X: `IsRegularScheme G.left` and `IsRegularScheme X.left`, using
  the recorded dependency INCLUDING local Noetherianity, not just regular stalks.
- Noetherian G and X: `IsNoetherian G.left` and `IsNoetherian X.left`.
  The Mathlib class is local Noetherianity plus compactness. Its theorem
  `isNoetherian_iff_of_finite_iSup_eq_top` identifies this with the node's finite
  cover by spectra of Noetherian rings.
- Smooth quotient map: `Smooth p.left`.
- Every point x of X and extension L/κ(x) gives a nonempty integral fibre:
  `GeometricallyIntegral p.left`. The definition quantifies all `Spec L → X`.
  Every such arrow factors uniquely through the residue field at its image point,
  so this is precisely the node's point-and-extension quantification. Conversely
  each x and extension supplies such an arrow. `IsIntegral` includes nonemptiness;
  no nonempty-fibre clause is discarded and no L-rational point is assumed.
- Conditional properness: `(IsBorelGroupScheme i → IsProper X.hom)`.
  `IsBorelGroupScheme` means closed, smooth, connected and solvable, maximal among
  such subgroups, with inclusion expressed by factorization. Its solvability uses
  `GroupSchemeDerivedLength`: termination at the terminal group and, at each step,
  `IsDerivedGroupScheme`, the smallest closed subgroup through which the actual
  commutator morphism factors. Thus it is exactly the definition in the node,
  including nonreduced test schemes, rather than abstract solvability of F-points.
  Smoothness, connectedness and closedness already occur as assumptions, so the
  implication does not strengthen the conditional hypothesis.

Recorded dependencies read and reused:

- `def-weil-field`: Mathlib `Field`, Algebra.Field.Defs.
- `def-weil-algebraic-closure`: Mathlib `IsAlgClosed`, FieldTheory.IsAlgClosed.Basic;
  algebraic closure data itself is not needed to state this theorem.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, Mathlib.CategoryTheory.Monoidal.Grp;
  the specialization to `Over (Spec F)` and group on Hom are supplied by the recorded
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` and its imports.
- `def-sc-group-scheme-subgroup`: `AlgebraicGeometry.IsClosedSubgroupScheme` in that
  same upstream module (and its parent `IsSubgroupScheme`, full signatures read).
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType` and `QuasiCompact`, Mathlib
  AlgebraicGeometry.Morphisms.FiniteType and .QuasiCompact.
- `def-sbc-smooth-morphisms`: `Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `def-weil-connected-scheme`: `ConnectedSpace`, Mathlib.Topology.Connected.Basic.
- `def-pc-scheme`: `Scheme` and its morphisms, Mathlib.AlgebraicGeometry.Scheme;
  affineness is the existing `IsAffine` predicate.
- `lem-sfb-algebraic-group-homogeneous-quotient`:
  `AlgebraicGeometry.exists_homogeneousQuotient`,
  Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient. Its full declaration and
  docstring were read; its precise projection, coset and lifting interfaces are used.
- `def-pc-integral-scheme`: `IsIntegral`, Mathlib.AlgebraicGeometry.Properties, used
  inside the existing `GeometricallyIntegral`, Mathlib.AlgebraicGeometry.Geometrically.Integral.
  Both full predicates and Mathlib's underlying `geometrically` definition were read.
- `def-weil-regular-scheme`: `IsRegularScheme`, Sheaf.AlgebraicGeometry.IsRegularScheme,
  defined as `IsLocallyNoetherian X ∧ IsRegular X` using the upstream regular-stalk class.
- `def-weil-proper-morphism`: `IsProper`, Mathlib.AlgebraicGeometry.Morphisms.Proper.
- Added the ALREADY LANDED `def-sfb-borel-subgroup-scheme` to `stmt_deps` under the
  standing permission to cite a landed notion. Its declaration `IsBorelGroupScheme`
  is in Sheaf.AlgebraicGeometry.GroupScheme.Borel. Read its dependency
  Sheaf.AlgebraicGeometry.GroupScheme.Semisimple, including `groupSchemeCommutator`,
  `IsDerivedGroupScheme`, `GroupSchemeDerivedLength`, and `IsSolvableGroupScheme`.
  No new node, dependency repair, or statement correction is needed.

All recorded proof-dependency modules are imported (without `public` when they only
serve the proof), including the smooth descent interfaces, geometric connectedness,
regularity, finite-type dimension, projective space, smooth orbit geometry, and
homogeneous orbit quotient geometry. Mathlib leaves are available through these
imports, including fpqc subcanonicity, finite type and surjective base change,
Noetherianity, and closed point residue fields. The three as-yet unstated proof nodes
`lem-trf-smooth-connected-fibre-normal-integrality`,
`lem-sfb-solvable-subgroup-flag-realization`, and `lem-sfb-solvable-proper-fixed-point`
have no recorded Lean modules to import; they remain named in the proof docstring.
They are proof prerequisites, not missing notions needed to type the statement.

Edge cases checked before writing: the trivial group and H = G give a one-point
quotient and fit every conclusion; a trivial H in a positive-dimensional nonsolvable
G does not trigger properness; solvable G has itself as its Borel and the same
one-point case; no characteristic restriction is imposed; no normality is imposed;
empty groups are excluded by the identity and connectedness, and empty X by the
surjective projection. Field-extension fibres need not have L-rational points;
nonempty integral schemes, not rational lifts, are asserted. The zero-step derived
series handles the trivial subgroup. Test schemes and test fields share universe u
with F, as in the recorded quotient and Mathlib geometric predicates, with no
independent smaller test universe or equality of distinct site universes.

Searches (2026-10-24):

- msearch.py leansearch: "A quotient of a smooth connected affine algebraic group by
  a Borel subgroup is proper and smooth". Eight hits, all abstract/topological
  quotient and Borel-measurable-space facts; none is this scheme theorem.
- msearch.py leanfinder: "Quotient of a smooth connected affine algebraic group by a
  smooth connected subgroup is smooth geometrically integral and is proper for a
  Borel subgroup". Eight hits, topological quotients; no matching theorem.
- msearch.py loogle: "AlgebraicGeometry.GeometricallyIntegral, AlgebraicGeometry.IsProper".
  One hit: `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`.
  This is proper-group commutativity, not quotient geometry.
- msearch.py grep: "[Bb]orel|[Ss]olvable.*[Gg]roup[Ss]cheme|[Gg]eometricallyIntegral"
  in Mathlib/AlgebraicGeometry: nine hits, identifying the existing geometric
  integrality predicate and proper-group commutativity, no Borel quotient theorem.
- rg of WeilConjectures and Sheaf for Borel/proper, solvability, commutators,
  GeometricallyIntegral and the proposed declaration: found the reusable Borel and
  derived-series definitions and existing consumers, no duplicate theorem. The
  item-id search in WeilConjectures had no hits. Search of dag/lean_names_upstream.json
  for the proposed declaration, IsBorelGroupScheme and IsSolvableGroupScheme had no
  upstream duplicate. DAG records identify the existing Borel/semisimple definitions.
- Read the cited Milne PDF via sandbox pdftotext: Corollaries 5.26--5.27,
  Proposition 7.15, Definition 17.6 and Theorem 17.9, including the closed flag orbit
  proof and conjugation using a fixed point. Source agrees with the statement.

No statement dispute or source correction. The only node changes are its `lean`
record and the additional already landed Borel definition dependency.

Validation: prescribed scompile.py compiled both the sandbox form and actual library
module form without errors or non-sorry warnings (2.5 s and 2.3 s respectively).
The file has `autoImplicit false`, explicit universe u, and no line over 100 columns.

## Second reading by Q23

The dispatcher explicitly forbids starting another agent; this section records the
worker's second pass over the node and Lean file, not an independent-worker review.
The maintainer's independent review is still required on the delivery.

On rereading both files, matched every assumption and conclusion to the correspondence
above. Checked the potentially lossy points explicitly: the given projection is kept;
cosets are tested on every scheme, not just F-points; local lifts use the recorded
fpqc presieve and equation; finite presentation includes QC and QS; regularity retains
local Noetherianity; nonemptiness is part of IsIntegral; geometric integrality of p
quantifies arbitrary residue-field extensions; properness remains conditional; and
Borel solvability uses the smallest scheme-theoretic commutator subgroup recursively.
No extra normality, affineness or finite-type assumptions on H, and no separatedness
or finite-type assumptions on X, were added. No mismatches were found and no statement
changes were made in this pass.
