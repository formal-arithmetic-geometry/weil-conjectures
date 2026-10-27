## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.NonzeroPencilDifferential` states
`AlgebraicGeometry.nonzero_pencil_differential_finite_etale`, with the complete
node conclusion, and six real helper definitions expanding its formulas. The
only postponed theorem is the main theorem; its proof is `sorry`, and its
docstring contains all eleven proof steps and their named dependencies. No data
is postponed. The node's mathematical statement is unchanged.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| An arbitrary field F, with no perfection or characteristic condition | `{F : Type u} [Field F]`; no other field assumption |
| A finite-type F-scheme C, smooth and projective | `f : C ⟶ Spec (.of F)`, `[Smooth f] [IsHProjective f] [LocallyOfFiniteType f] [QuasiCompact f]` |
| Geometrically integral, integral, dimension one | `[GeometricallyIntegral f] [IsIntegral C]`, `_hdim : topologicalKrullDim C = 1` |
| An invertible module M | `(M : C.Modules) [M.IsInvertible]` |
| The ordered sections s,t generate M | `s : ULift (Fin 2) → M.sections`, `hs : Epi (M.freeHomEquiv.symm s)`; entries 0 and 1 are the two sections |
| h is their coordinate morphism | `_hh : h = ProjectiveSpace.homOfGeneratingSections _ f M s hs`; this merely names the defined morphism, and adds no restriction on the pair |
| The target is smooth, separated, integral, dimension one | The first four conjuncts; its finite type and quasi-compact structure are also supplied by the existing projective-space properness instance |
| The global alternating differential | `∃! δ : Γ(f.relativeDifferentials ⊗ (M ⊗ M), ⊤)` satisfying `pencilDifferentialFrameFormula`; on every frame `e` and coefficients `a,b`, its restriction is `tmulSection (b • d a - a • d b) (tmulSection e e)` |
| t≠0 and s≠0 are the two target chart preimages | First clause of `pencilDifferentialChartFormula`, equating each chart preimage with the recorded `nonvanishingLocus` |
| The pulled coordinate is s/t and d(s/t)=(t ds-s dt)/t², and the other chart formula | Remaining clause of `pencilDifferentialChartFormula`; it quantifies over distinct denominator/numerator indices in both orders, a local frame, its numerator coefficient `a`, and an invertible denominator coefficient `b`. The coordinate pulls back to `a * ↑(b⁻¹)` and its derivative is `↑(b⁻¹)^2 • (b • d a - a • d b)`. Reversing the indices gives the negative alternating expression on the other chart |
| dh≠0 iff δ≠0 | The nonzero equivalence for the dependency's canonical `Scheme.Hom.relativeDifferentialsPullbackMap` (its target is Ω for h composed with the projection; `_hh` identifies that composite with f) |
| If δ≠0 then h is finite and surjective | `δ ≠ 0 → IsFinite h ∧ Surjective h ∧ ...` |
| Étale on a nonempty source open | `∃ V : C.Opens, (V : Set C).Nonempty ∧ Etale (V.ι ≫ h)` |
| Every algebraic closure K/F | `∀ (K : Type u) [Field K] [Algebra F K] [IsAlgClosure F K]` |
| The geometric source and module are the actual base changes | `pullback f (Spec.map (CommRingCat.ofHom (algebraMap F K)))`, and `tensorPullback` of its first projection |
| The geometric sections are the pullbacks of s,t | `pencilPullbackSection` uses the unit of the uniquely normalized `tensorPullbackSectionAdjunction`, then the existing `homOfGlobalSection` and `unitHomEquiv` to make a compatible section |
| h_K is exactly the geometric map | `pencilGeometricConclusion` gives the unique hK with both projective-space base-change projection equations. These are the universal-property characterization of the base change of the specified coordinate morphism, not an arbitrary morphism |
| δ(s_K,t_K)≠0 | `pencilGeometricMapConclusion` uniquely characterizes δK by the identical frame formula with the pulled-back pair, and asserts δK≠0 |
| Both geometric sections are nonzero | `∀ i : ULift (Fin 2), (s i).val (op ⊤) ≠ 0` in the geometric predicate |
| r=h_K^*z is a rational function | `pencilAffineCoordinateGerm hK hη` is the actual generic germ of `hK.app` on `coordRatio ... ⟨1⟩ ⟨0⟩`. The conclusion supplies `hη`, so this germ is defined on an open containing the generic point |
| dr≠0 | `KaehlerDifferential.D K D.functionField` applied to that germ is nonzero, using the algebra structure of the explicitly inlined scalar map `((Scheme.ΓSpecIso (.of K)).inv ≫ b.appTop ≫ D.presheaf.germ ⊤ (genericPoint D) trivial).hom` |
| r is not in K | The germ differs from the value at `c` of that same inlined map for every `c : K` |
| r defines exactly h_K via the curve/function-field correspondence | Every K-morphism χ with generic image in the z-chart and the same coordinate germ equals hK. Since r is nonconstant, this is precisely uniqueness for the embedding z↦r, and includes the identification with the actual base-changed pencil |
| The projection P¹_K→P¹_F is flat, surjective, quasi-compact | The three properties of `ProjectiveSpace.map (ULift (Fin 2)) (Spec.map ...)`, asserted for every algebraic closure even when δ=0 |
| Finiteness after base change descends | The geometric predicate asserts `IsFinite hK` and the main conclusion asserts `IsFinite h`; proof step 11 explicitly applies the recorded fpqc descent theorem to this projective-space base-change square |

The tensor square is written `M ⊗ M`, as the node's positive-power tensor
convention specifies. The two `∃!` section clauses express the uniquely glued
section directly; there is no choice from an existence statement lacking a
characterization. The helpers are expansions of objects and clauses introduced
by this very node, rather than new independent notions or private copies of the
dependencies. No new definition node or dependency repair is needed.

Dependency declarations read and used:

| Dependency | Module and declaration |
| --- | --- |
| def-weil-field | `Mathlib.Algebra.Field.Defs`: `Field` |
| def-sbc-smooth-morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` |
| def-kun-projective | `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `AlgebraicGeometry.IsHProjective` |
| def-pc-geometrically-irreducible | `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `AlgebraicGeometry.GeometricallyIntegral` |
| def-pc-integral-scheme | `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral` |
| def-weil-finite-type-morphism | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`: `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact` |
| def-kun-topological-krull-dimension | `Mathlib.Topology.KrullDimension`: `topologicalKrullDim` |
| def-sc-invertible-module | `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `AlgebraicGeometry.Scheme.Modules.IsInvertible` |
| def-weil-pbc-generating-sections | `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`: `SheafOfModules.GeneratingSections`; its epimorphism condition is used directly on the fixed two-entry family |
| def-weil-pbc-morphism-to-projective-space-by-sections | `Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections`: `AlgebraicGeometry.ProjectiveSpace.homOfGeneratingSections` |
| def-weil-pbc-kahler-differentials | `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential.D` |
| def-pur-sheaf-tensor-product | `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: `SheafOfModules.cochainModulesMonoidal`; scheme tensor and section APIs reuse `WeilConjectures.AlgebraicGeometry.Modules.Invertible` and `.TensorSection` |
| def-weil-finite-integral-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite` |
| def-weil-surjective-morphism | `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective` |
| def-weil-etale-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale` |
| def-weil-algebraic-closure | `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosure` (imported via `.AlgebraicClosure`) |
| def-sc-function-field | `WeilConjectures.AlgebraicGeometry.FunctionField`: its documented integral-scheme specialization reuses Mathlib `AlgebraicGeometry.Scheme.functionField`, the generic stalk |
| def-weil-flat-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat` |
| def-pc-base-change | `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the documented existing scheme pullback and its projection equations, `CategoryTheory.Limits.pullback` |
| def-sc-relative-differential-sheaf | `WeilConjectures.AlgebraicGeometry.Modules.Differentials`: `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`, `.relativeDifferentialsDerivation` |
| def-a1-relative-differentials-pullback-map | `Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap`: `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackMap` |
| def-pc-module-pullback | `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction`, with the existing tensor-pullback functor |
| Scalar map for dr and constants | Inlined from `Scheme.ΓSpecIso`, `b.appTop`, and `D.presheaf.germ ⊤ (genericPoint D) trivial`; these existing spectrum, scheme-map and function-field operations compose to the canonical map `K →+* D.functionField` |
| def-sc-p1-standard | `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`: the recorded `ProjectiveLine` and its standard charts; coordinates reuse `.OfInvertible`'s `ProjectiveSpace.coordRatio` |

The two already landed nodes `def-pc-module-pullback` and `def-sc-p1-standard`
are added to stmt_deps because their interfaces occur in the statement. They
were already proof dependencies. The proper-curve correspondence is retained
only in proof_deps and as a plain proof import. All
other node fields, including the complete statement and proof, are preserved.
Stated proof dependencies are imported, including the generic cotangent
criterion, projective-space charts and functor of points, proper-curve
correspondence and finite fpqc descent. The two proof-only nodes
`lem-trf-relative-differential-sheaf-base-change` and
`lem-sfb-proper-dimension-one-noncontraction-finite` have no recorded module or
Mathlib match in this read clone, so there is no module to import for them;
they supply no missing notion needed to state this item.

Edge cases checked before writing:

- Empty or dimension-zero C is excluded by integrality and dimension one,
  as the node requires; empty local frame opens are allowed and the formulas
  reduce to the unique equality in zero section modules.
- A zero member of the generating pair and constant pencils are allowed.
  Their alternating differential vanishes, and only the conditional finite-map
  conclusion is inactive; target geometry, both chart rules, gluing, the
  differential equivalence and the fpqc projection properties remain asserted.
- In characteristic p, a Frobenius pencil has zero differential. No separability
  is incorrectly inferred in that case. Characteristic two retains the same
  alternating formula with its correct sign, since the proof uses cancellation,
  not division by two.
- Algebraic closures may have infinite degree. No finite-extension hypothesis
  is imposed, and quasi-compactness concerns the scheme projection, not its
  degree. All fields and schemes range in the arbitrary common universe `u`;
  `ULift (Fin 2)` is the same two-element coordinate set in that universe.
- Coordinate denominators are required to be units only on the local open
  where the corresponding member trivializes M; the chart preimage equality
  ensures that these opens are exactly the source's nonvanishing charts.
- The germ is formed at the actual generic point, with the proved membership
  carried explicitly; no arbitrary element of the function field replaces r.

Searches for an existing statement (all through the prescribed tool or read-only source searches):

| Tool | Query | Result |
| --- | --- | --- |
| msearch leanfinder | `nonzero pencil differential generating pair line bundle finite surjective generically etale curve` | Eight hits on Weierstrass nonsingularity and standard smooth presentations; none states this lemma |
| msearch loogle | `KaehlerDifferential.D, AlgebraicGeometry.ProjectiveSpace` | No hits; ProjectiveSpace not known to the remote Mathlib-only index |
| msearch grep, AlgebraicGeometry | `pencil\|Pencil\|generically.*[Ee]tale` | Zero hits |
| msearch leansearch | `A nonzero differential of a pencil on a smooth projective integral curve gives a finite surjective generically etale morphism to the projective line` | Eight hits on etale definitions and unrelated manifold differentials; none states the result |
| rg, WeilConjectures and Sheaf | `pencil`, `Pencil`, `pencilDifferential`, `alternatingDifferential`, `wronskian`, `Wronskian` | Existing pencil coordinate constructions and generic differential criterion found and reused; no alternating-section statement or complete result |
| rg, Mathlib | Same alternating differential names | Only polynomial Wronskian material, which is a different notion |
| rg, WeilConjectures | Exact item ID | No hits |
| rg, upstream name index and sources | `pencilDifferentialFrameFormula\|nonzero_pencil_differential_finite_etale` | No existing declaration clashes |

The source paragraphs actually read are `curves.tex` Tag 0C1C (nonzero df
criterion), Tag 0BY1 (the fully faithful generic-stalk correspondence), and Tag
0CCL (finiteness by noncontraction), alongside the existing chart and differential
source docstrings. The current blueprint's ctf-stability statement was read to
check that this auxiliary node does not change a unit statement.

Validation: prescribed `scompile.py` compiled the sandbox probe and the named
library module cleanly, both in about 3.3 seconds. No other compiler or build was
used. No STATEMENT-DISPUTED flag or statement correction is needed.

## Second reading by Q154

Reopened the complete node and final module after compilation, independently of
the initial drafting pass. This is the dispatcher's single-worker second pass;
the maintainer supplies the independent review, and no second agent was started.
Checked each row of the correspondence above against the signatures and the six
helper bodies. In particular, the second chart uses the reversed numerator and
denominator rather than the same sign, the differential is the recorded
canonical map, and the geometric r is the actual pulled coordinate germ.
The nested uniqueness clauses introduce neither an arbitrary section nor an
arbitrary geometric morphism. The initial elaboration errors were repaired by
explicit tensor-section arguments, explicit chart coordinate types, splitting
long geometric clauses into transparent predicates, and exposing the modules
that supply statement declarations. No mathematical hypothesis or clause was
changed, and all universes and variables are bound explicitly.

## Returned delivery repair

H2, immutable returned head `1ed37c62d390`: removed the theorem node
`lem-sfb-proper-curve-function-field-morphisms` from the proposed additions to
stmt_deps. In both scalar-map occurrences in `pencilGeometricMapConclusion`,
expanded the definition verbatim to the composition of `Scheme.ΓSpecIso.inv`,
the structure morphism's `appTop`, and the generic germ. Thus dr and the
nonconstant assertion use only existing definition-node operations. Changed the
correspondence module's import from public to plain; its theorem remains
available for the proof and its proof_deps entry is preserved. No declaration,
mathematical statement, hypothesis, or conclusion is added or removed.

Compared the retained delivered node with current main, then rebuilt the node
copy from current main with only the repaired lean record and the two permitted
definition dependencies added. The delivery wrapper rebases its worktree on the
current server branch. A second reading of the two expanded expressions confirms
that they are definitionally identical to the former scalar map, and that the
proper-curve theorem's conclusion is needed only for proof step 8.
