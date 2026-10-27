## Worker report

The module `Sheaf.AlgebraicGeometry.AmpleCurveFirstJetInterpolation` states
`AlgebraicGeometry.Scheme.Modules.exists_ample_curve_first_jet_interpolation`.
Its only proof is `sorry`. There are no new definitions, new nodes, dependency
repairs, or statement corrections. The informal statement and proof are unchanged.
The two added statement dependencies already have usable recorded declarations:
`def-sbc-closed-immersion-ideal-sheaf` and `def-pc-module-pullback`. They record
the closed-immersion ideal and tensor pullback already used in the informal
statement. The module uses the section-normalized adjunction owned by the latter
definition node to state the canonical restriction on global sections.

Hypothesis and conclusion matching:

| Node clause | Lean rendering and interpretation |
| --- | --- |
| Algebraically closed field k | `(k : Type u) [Field k] [IsAlgClosed k]`. No characteristic restriction. |
| A k-scheme D | `(D : Scheme.{u}) [D.Over (Spec (.of k))]`; its structure morphism is `D ↘ Spec (.of k)`. |
| Smooth, proper, integral, finite type | `[Smooth ...] [IsProper ...] [IsIntegral D]`. `IsProper` extends `LocallyOfFiniteType` and implies `QuasiCompact`; hence it includes the node's finite-type hypothesis. These properties are not extra binders. |
| Dimension one | `hdim : topologicalKrullDim D = 1`. This is topological Krull dimension, not a choice of relative-dimension datum. |
| Ample invertible A | `(A : D.Modules) [A.IsInvertible] (hA : IsAmple D A)`, using the existing scheme-module definitions. |
| Nonempty finite set of distinct rational closed points, with x in T | `T : TopologicalSpace.Closeds D`, `hT : (T : Set D).Finite`, `hclosed : ∀ y : T, IsClosed ({y.val} : Set D)`, and `x : T`. A subset has distinct elements; `x` supplies nonemptiness. Finite unions of closed points are closed, so bundling the set as a `Closeds` adds no hypothesis. Every closed point of a finite-type scheme over an algebraically closed field is k-rational, so no extra rational-point choice is needed. Conversely the node's rational closed points supply precisely these binders. |
| R_y and its maximal ideal; these are DVRs with the described factorization | `D.presheaf.stalk y.val`, `IsLocalRing.maximalIdeal (...)`, and the first conjunct `∀ y : T, IsDiscreteValuationRing (...)`. Mathlib defines DVR as a local principal ideal domain that is not a field, equivalent to the node's nonzero principal maximal ideal and unique power/unit factorization (Stacks 00PD). The domain instance comes from integrality of D. |
| Finite closed subscheme Z with support T and local rings R_y/m_y² | The actual constructed scheme is `(Scheme.IdealSheafData.vanishingIdeal T ^ 2).subscheme`, with its actual `subschemeι`. The conclusion asserts `support = T`, `IsFinite (subschemeι ≫ structureMorphism)`, and that each stalk-map kernel is the square of the ambient maximal ideal. The map is surjective on stalks because `subschemeι` is a closed immersion; consequently its local ring is canonically the specified quotient, with the correct ambient ring map. These clauses characterize the Z named in the node rather than supplying an arbitrary quotient isomorphism. |
| I_Z | `(Scheme.IdealSheafData.vanishingIdeal T ^ 2).toModules`, the existing kernel construction for the defining ideal. |
| n0 at least 1, every n at least n0 | `∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ...`. All subsequent three eventual assertions and interpolation use this same bound. |
| A tensor n globally generated | `Nonempty (SheafOfModules.GeneratingSections (A.tensorPow n))`. This is the recorded generating-sections structure, not surjectivity of all section evaluations on arbitrary opens. |
| H¹(D,I_Z tensor A tensor n)=0 | `IsZero ((RingedSpace.moduleCohomology D.toRingedSpace 1).obj (tensorObj I_Z (A.tensorPow n)))`. This is right-derived module global sections, exactly the cohomology specified by the dependency, not bare abelian-sheaf Ext. |
| Global restriction onto Z surjective | `Function.Surjective (((tensorPullbackSectionAdjunction i).unit.app (A.tensorPow n)).app ⊤ ≫ ((tensorPullback i).obj (A.tensorPow n)).presheaf.map (homOfLE i.preimage_top.ge).op)`, with `i = (vanishingIdeal T ^ 2).subschemeι`. This is the section-normalized adjunction unit on global sections, followed by restriction from the inverse image of top to top. Its actual target is global sections on Z of the existing tensor pullback. |
| Any component frames | `e : ∀ y : T, (R_y ⧸ m_y^2) ≃ₗ[R_y] (L_y ⧸ m_y^2 • ⊤)`. The two R_y-actions factor through R_y/m_y², so these are exactly the equivalences over the quotient ring, or frames of the rank-one module on the singleton component. The generator is `e y 1`. Invertibility ensures the frame types are inhabited. No stalk frame, or chosen lifting of a frame, is imposed. |
| Any generator u of m_x | `(v : D.presheaf.stalk x.val)` with `maximalIdeal ... = Ideal.span {v}`; the letter v avoids confusion with universe u. Nonzeroness follows from the DVR assertion, not an additional assumption. |
| A global section with coefficient u modulo m_x² | `∃ a : Γ(A.tensorPow n, ⊤), (e x).symm (Submodule.Quotient.mk (germ a)) = Ideal.Quotient.mk _ v`. This uses the actual germ and quotient map. |
| Coefficient 1 at every other marked point | `∀ y : T, y ≠ x → (e y).symm (Submodule.Quotient.mk (germ a)) = 1`. |
| Simple zero at x | The germ belongs to `m_x • ⊤` and does not belong to `m_x^2 • ⊤`. In any local rank-one frame this is exactly coefficient membership in m_x minus m_x². It is independent of a lift of the specified component frame. |
| Nonzero at all other marked points | `∀ y : T, y ≠ x → y.val ∈ nonvanishingLocus (A.tensorPow n) a`, the recorded nonzero residue-fibre predicate. |

Dependency declarations read and reused:

- Mathlib: `Field` (`Mathlib.Algebra.Field.Defs`); `IsAlgClosed`
  (`Mathlib.FieldTheory.IsAlgClosed.Basic`); `AlgebraicGeometry.Smooth`
  (`Mathlib.AlgebraicGeometry.Morphisms.Smooth`); `AlgebraicGeometry.IsProper`
  (`Mathlib.AlgebraicGeometry.Morphisms.Proper`); `LocallyOfFiniteType` and
  `QuasiCompact` (their morphism modules); `AlgebraicGeometry.IsIntegral`
  (`Mathlib.AlgebraicGeometry.Properties`); `topologicalKrullDim`
  (`Mathlib.Topology.KrullDimension`); and `SheafOfModules.GeneratingSections`
  (`Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`).
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `tensorObj`, `tensorPow`.
  The tensor is the existing sheafification/localization tensor; the recorded
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` is publicly
  imported as required by `def-pur-sheaf-tensor-product`.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple` and `nonvanishingLocus`.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`:
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`; its public import
  `WeilConjectures.Topology.RingedSpaceModuleCohomology` provides the actual
  `RingedSpace.moduleCohomology` used here.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `Scheme.Hom.ker`,
  `Scheme.IdealSheafData.vanishingIdeal` and the existing ideal power operations;
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` supplies `subscheme` and
  `subschemeι`. `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`
  supplies `Scheme.IdealSheafData.toModules`, the kernel of the structure-sheaf
  map to the closed subscheme's pushforward.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction`, reusing
  the upstream explicit `tensorPullback`. The canonical global restriction is
  stated directly using this definition node's `tensorPullbackSectionAdjunction`:
  evaluate its unit at the module and top, then compose with the presheaf
  restriction along `i.preimage_top.ge`. Its normalization sends m to `1 tensor m`
  by `existsUnique_tensorPullbackSectionAdjunction`. No theorem-node conclusion
  or independently chosen adjunction is used as the owner of this map.
- `Mathlib.Algebra.Category.ModuleCat.Stalk`: the existing module structure on
  `TopCat.Presheaf.stalk M.val.presheaf y` and the germ maps.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`
  and the proof input `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`.

Every recorded proof-dependency module is imported, publicly when already a
statement dependency, and otherwise as a plain proof import. This includes the
Noetherian, coherence, regular-curve, Cartier-point, ample-generation,
Serre-vanishing, and exact-stalk modules. The declaration docstring contains all
eight proof steps and their input node names. No new proof lemma was added.

Source inspection: read `literature/stacks-project/coherent.tex`,
`lemma-kill-by-twisting` (02O1), including its reduction to affine-base H^p;
`properties.tex`, `proposition-characterize-ample` (01Q3), especially (1) to (7);
and `cohomology.tex`, `section-cohomology-sheaves` (01DZ), the module-cohomology
universal delta-functor. The local DVR and prescribed-jet arguments are the
node's existing agent deductions, retained step by step. This is an auxiliary
node, not the unit's statement.

Edge cases checked before writing:

- Empty D is excluded by integrality and by the chosen marked point. Empty T
  is excluded exactly by `x : T`; no accidental restriction to at least two
  marked points occurs. For T={x}, all y≠x clauses are vacuous as required.
- On P¹ with A=O(d), d>0, and m marked points, the ideal twist is O(dn-2m);
  H¹ vanishes for dn≥2m-1 and arbitrary first jets can be imposed. This tests
  both the square of the ideal and the one uniform eventual bound.
- Tensor power zero is defined by the existing `tensorPow`; the promised
  range begins at n0≥1. The assertion is for every n above n0, not one power.
- No characteristic-zero hypothesis or division by a group order appears;
  the result and its local cancellation proof work in every characteristic.
- A quotient-frame change is any unit modulo m². Such a unit lifts to a unit
  in the local ring. Thus quantifying over quotient frames does not silently
  restrict to frames already chosen over D. The simple-zero conclusion is
  invariant under every such change.
- All objects use an explicit universe u. No test-algebra quantification,
  smaller index universe, auto-implicit parameter, local notation, or local
  instance is used. No definitions have postponed data.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder "High powers of an ample invertible sheaf on a
  smooth proper curve interpolate first order jets at finitely many rational
  closed points"`: 8 hits, including affine localization/power-extension
  lemmas and Weierstrass coordinate-ring facts; no matching interpolation
  statement. Their names and summaries were read in the search output.
- `msearch.py ... loogle 'AlgebraicGeometry.Scheme, "jet"'`: OK, 0 hits.
- `msearch.py ... leansearch "Serre vanishing and surjectivity of global
  sections of large ample tensor powers on a proper curve onto a finite
  first infinitesimal neighbourhood"`: 8 hits, including
  `StructureSheaf.toBasicOpen_surjective`, affine-site presieve surjectivity,
  localization/power-extension lemmas, a limit-sections lemma and the
  Zariski-local surjectivity predicate; none states this result.
- `msearch.py ... grep 'first.?[Jj]et|jet.*interpol|Serre.*vanish|serre.*vanish|IsAmple'
  AlgebraicGeometry`: OK, 0 hits in Mathlib.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for first jets,
  interpolation, prescribed-point data, ideal-module bridges and stalks found
  the reused APIs above and the nearby prescribed-point jet-system theorem.
  The latter concerns a projective compactification and the kernel of residue
  evaluation, with cotangent-space jets; it is not this ample-curve theorem
  or its simultaneous full R/m² restriction conclusion.
- `grep -rn 'lem-sfb-ample-curve-first-jet-interpolation'
  lean/WeilConjectures`: no hits. The proposed full declaration name also has
  no hit in `dag/lean_names_upstream.json`, Mathlib, WeilConjectures or Sheaf.
- DAG searches for first-jet and ample-curve interpolation found this node,
  its consumer `lem-sfb-separating-pair-open`, and the distinct two-section
  pencil / prescribed-point-system nodes. No duplicate statement was found.

Original validation: `scompile.py Q24 lem-sfb-ample-curve-first-jet-interpolation
<module>` compiled the original sandbox module (6.6 seconds) and the module
at its delivered name (4.1 seconds), with no errors or warnings. Repair validation
is recorded below. During drafting,
the existing module-stalk scalar instance required the explicit bundled
`M.val.presheaf` stalk with its carrier coercion. Removing redundant finite-type
binders fixed the overlapping-instance warning without changing the hypotheses.
The final theorem has no `let`/hidden-have signature terms.

## Second reading by Q24

I reopened the node and the completed Lean file for a second clause-by-clause
pass. The dispatcher explicitly forbids starting other agents; this is the
worker's second pass, not a claim of independent authorship. The maintainer's
independent review remains the external review specified in the assignment.

I checked the quantifier scope: the same n0 works for all later n, and each such
n permits every component frame and every generator of m_x. The section a
depends on that frame and generator. I checked that the target of the asserted
surjection is sections on the actual first-jet subscheme of the actual tensor
pullback, and that the component coefficients use germs modulo m², not residue
values alone or cotangent vectors without a constant term. I checked the two
simple-zero membership clauses and the nonvanishing predicate against their
definitions. I checked that the finite-support and local-ring clauses describe
the square of the reduced ideal and do not assume DVR structure in advance.
The source already assumes finite type; properness implies it here. All these
clauses match the node. No mathematical mismatch or disputed statement was
found, and no statement change was made during this pass.

## Repair of returned delivery 9cc3e43068f

The single H2/H4 return requested that the section map be owned by its
canonical definition node, rather than by the unrelated theorem node
`lem-sc-etale-qcoherent-presheaf-functorial`. I replaced `tensorSectionsUnit`
with exactly the explicit composite requested by the maintainer: the unit of
`tensorPullbackSectionAdjunction i`, at `A.tensorPow n` and top, followed by
the pullback presheaf restriction along `i.preimage_top.ge`, for the actual
first-jet closed immersion i. I removed both the theorem node from stmt_deps
and the direct import of `EtaleTensorSections`. The `lean.statement` record
was regenerated from the revised signature, and its note and this report now
name the correct owner. No other mathematical clause or informal statement
changed.

For the advisory, `toModules` is the existing definition in
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`: it is the kernel
of `toPushforwardSubscheme`, so it is the ideal module of the closed immersion.
That owning module is directly publicly imported. The two remaining additions
to stmt_deps are definition nodes for notions already present in the informal
statement (its I_Z and its restriction A^n|_Z), as the return acknowledges for
`def-pc-module-pullback`. No theorem node was substituted for their owning
definitions; no node statement or proof was changed.

I compared the retained sandbox to the current shared node: outside lean and
stmt_deps it is identical. The shared node still has no lean record, so the
required delivery wrapper will rebase this substantive repair on current main.
The mathematical source edit relative to the returned version is the requested
canonical-map replacement and removal of the now-unneeded import. An explicit
source/target type annotation fixes the composite as the global-section arrow.
Elaboration keeps tensor pullback and its adjunction folded using local
irreducibility and the upstream transparency options; a theorem-scoped
`maxHeartbeats 800000` accommodates the explicit composite. The required
60-second wall-clock limit is unchanged.

Second reading of the repair: with the node, revised file, and full
`tensorPullbackSectionAdjunction` declaration open, I checked that the unit
lands over i^{-1}(top), and the final presheaf map identifies this with top
without changing the unit normalization. All arguments and universes remain
explicit, the same n0 governs all eventual conclusions, and the quotient-frame
and simple-zero clauses are untouched. This is an in-thread rereading under
the dispatcher's no-subagents rule; the maintainer supplies independent review.

Repair validation: the explicit composite compiled in 14.2 seconds in the
sandbox and 13.9 seconds at its library name. That check exposed only an
unscoped-heartbeat style warning; the option is now scoped to this declaration
with an explanatory comment. The final clean check and delivery preflight are
run on that corrected version through the prescribed wrappers.

Final `scompile.py` check: sandbox 14.1 seconds, delivered library module
14.4 seconds; exit code 0, with no errors or warnings.
