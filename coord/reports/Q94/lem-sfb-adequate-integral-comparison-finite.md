## Worker report

The module `Sheaf.AlgebraicGeometry.AdequateIntegralComparisonFinite` states
`CategoryTheory.adequate_integral_comparison_finite`, with its sole proof `sorry`.
It defines no new notion. The theorem docstring gives all six proof steps of the
DAG node, with their named prerequisites and the section-algebra comparison.
The natural-language statement, proof and proof dependencies are unchanged.

Source read: Alper, *Adequate moduli spaces and geometrically reductive group
schemes*, arXiv:1005.2398v3, Lemma 8.3.1, printed p.39, and Section 2, printed p.7:
https://arxiv.org/pdf/1005.2398v3 . The lemma's (a), (b), (c) are precisely the
representable/quasi-finite/separated, integral and closed-point assumptions.
Section 2 explicitly supplies the quasi-compact separated diagonal convention.
The node specializes to finite-type stacks over a field, and these hypotheses
are retained as written. No statement correction or dispute was needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field is `(k : Type u) [Field k]`. All schemes are in `Scheme.{u}`.
- U and V are `BasedCategory.{v₁, w₁}` and `BasedCategory.{v₂, w₂}` over
  `Over (Spec (.of k))`, with `hU` and `hV : IsAlgebraicModuliStack ...`.
  The four stack universes remain independent of one another and of u.
- Finite type of U and V is `hUft` and `hVft`: existence of a smooth surjective
  scheme atlas `a` (`IsSmoothModuliAtlas`), whose structural morphism is
  `LocallyOfFiniteType T.hom ∧ QuasiCompact T.hom`. Smooth refers to the map
  from the atlas to the stack, not smoothness of the stack over k. The
  existing `HasSmoothFiniteTypeModuliAtlas` is deliberately not used: it is
  a DM-specific predicate imposing an étale atlas and smoothness over k.
- P and Q are the existing `AlgebraicSpace (Spec (.of k))`. The maps p and q
  are `BasedFunctor` into their existing discrete fibred groupoids. `hp` and
  `hq` use `IsAdequateModuliSpace` with the corresponding algebraic-stack
  proofs. This includes qcqs, the canonical structure-sheaf isomorphism,
  and the full power-lifting condition on every affine étale base change.
- The k-morphisms are `f : BasedFunctor U V` and `g : P ⟶ Q`. The specified
  comparison is actual data `square : ModuliTwoIso (f.comp q)
  (p.comp (discreteModuliMap g.hom.hom))`, so qf is identified with gp over
  the identity on the base, rather than unrelated maps or point functions.
- `hf` quantifies over every scheme T and every map t to V. Its Z and a
  together with `HasSpaceBaseChange f T t Z a` express representability by
  algebraic spaces and identify the actual pullback projection. No scheme
  representability of f itself is assumed.
- Quasi-finiteness in `hf` is `AlgebraicSpace.MapIsQuasiCompact a` together
  with `MapToSchemeIsLocally (fun _ _ b ↦ LocallyOfFiniteType b ∧
  LocallyQuasiFinite b) Z T a`. Thus the actual space projection is
  quasi-compact, and every étale scheme chart is locally of finite type
  and locally quasi-finite. For algebraic spaces this is exactly finite
  type with finite geometric fibres. In particular, Mathlib's
  `LocallyQuasiFinite` alone does NOT require local finite type; the latter
  is explicitly retained. Scheme characterization:
  `AlgebraicGeometry.locallyQuasiFinite_iff_finite_preimage_singleton`
  under local finite type and quasi-compactness, and stability under base
  change. Quasi-compactness is required for the space projection, not for
  every possibly infinite étale chart.
- Separatedness in `hf` is `AlgebraicSpace.MapToSchemeIsSeparated Z T a`,
  which is representability of the actual relative diagonal by closed
  immersions, not merely separation of the underlying point map.
- `hg` uses `AlgebraicSpace.IsRepresentableWith
  (fun _ _ a ↦ IsIntegralHom a.left) g.hom.hom`. On every scheme base
  change the representing scheme projection is integral, as required.
- Points are the existing `ModuliPoints`, the quotient of field objects
  by arrows and their equivalence closure. `moduliPointMap f` is the
  quotient map induced by f itself. `hclosed` maps closed singletons to
  closed singletons using the existing instance
  `moduliPointTopologicalSpace` on U and V (ordinary `IsClosed`). It does not
  use the étale-atlas closedness test intended only for DM stacks.
- The Section 2 convention is `hUdiag` and `hVdiag`: on every scheme test
  of the actual diagonal there is an algebraic-space presentation with
  its specified projection a, and a is quasi-compact and separated.
  The diagonal is `moduliRelativeDiagonal (moduliBaseStructure U)` or V;
  the existing `moduliBaseStructure` is the canonical structure morphism
  to the identity category over `Sch/k`, which represents the base.
  Quasi-compactness is exactly the existing `MapIsQuasiCompact` used by
  the recorded stack qcqs interface. This does not assume a finite,
  proper, unramified, or scheme-representable diagonal.
- The conclusion `IsRepresentableFiniteModuliMap f` means every scheme
  2-base change is represented by a scheme finite over that same test,
  with the projection identified by an isomorphism over the base.

Dependency declarations used (all read with their signatures and docstrings):

- `Mathlib.Algebra.Field.Defs`: `Field` (`def-weil-field` is a mathlib leaf).
- `Sheaf.AlgebraicGeometry.AdequateModuliSpace`:
  `CategoryTheory.IsAdequateModuliSpace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`:
  `AlgebraicGeometry.AlgebraicSpace`, `.IsRepresentableWith`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite` and `.Integral`:
  `AlgebraicGeometry.IsFinite`, `.IsIntegralHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`:
  `AlgebraicGeometry.LocallyQuasiFinite` and the finite-fibre characterization.
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`: its recorded
  `IsQuasiSeparatedAlgebraicModuliMap` and `IsQuasiCompactAlgebraicModuliMap`
  are used inside `IsAdequateModuliSpace`; their `MapIsQuasiCompact` is reused
  explicitly on all representable space tests.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`, `.IsSmoothModuliAtlas`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `HasSpaceBaseChange`, `ModuliTwoIso`, `discreteModuli`, `discreteModuliMap`,
  `moduliTwoFiberProduct`; ordinary `BasedCategory`, `BasedFunctor` are Mathlib.
- `Sheaf.AlgebraicGeometry.RelativeModuliInertia`: `moduliBaseStructure`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`:
  `ModuliPoints`, `moduliPointMap`, `moduliRelativeDiagonal`. These particular
  definitions are general fibred-groupoid constructions and impose no DM condition.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`:
  `AlgebraicSpace.MapIsQuasiCompact`, `.MapToSchemeIsLocally`,
  `.MapToSchemeIsSeparated`.
- `Sheaf.AlgebraicGeometry.FiniteStackSchemeTests`:
  `CategoryTheory.IsRepresentableFiniteModuliMap` (no DM hypothesis).
- `Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen`:
  `CategoryTheory.moduliPointTopologicalSpace`, the existing topology instance
  owned by `def-sfb-stack-point-topological-space`.

The six added statement dependencies are already landed nodes owning the
interfaces above: `def-sfb-algebraic-moduli-stack`,
`def-sfb-relative-moduli-inertia`, `def-sfb-dm-stack-morphism-properties`,
`def-sfb-proper-curve-moduli`, `def-sfb-finite-stack-scheme-tests`, and
`def-sfb-stack-point-topological-space`. No dependency record is changed.
The topology definition module is a public import for the closed-point hypothesis.
The smooth-presentation theorem stays in proof_deps and its module is a plain
proof import; none of its declarations is needed to state the theorem.
AdequateModuliSpace publicly exposes StackQuasiCoherentAlgebra,
and FiniteStackSchemeTests exposes the Mathlib finite/integral interface, so
already-available proof prerequisites need no redundant imports. The remaining
unstated proof prerequisites have no Lean records in the read clone;
no import of an unstated module is invented.

Edge cases checked before drafting: empty U and empty atlas are permitted;
there is no nonempty or surjectivity requirement on f or g; identity maps are
allowed; no characteristic restriction or algebraic closure of k is imposed;
nonreduced schemes and inseparable field extensions are retained; geometric
fibres are controlled by quasi-finiteness, not by counting field-valued
sections; non-DM stacks are permitted and smooth atlases are used; an
arbitrary integral g need not initially be finite; neither stack's diagonal
is assumed finite or proper. Algebraic-space scheme tests stay in universe u,
with no artificially smaller test universe and no identification of the stack
object or morphism universes. Every variable is bound with autoImplicit false.

Searches (2026-10-24):

- `msearch.py ... leanfinder`: "A representable quasi finite separated morphism
  between finite type algebraic stacks with adequate moduli spaces is finite if
  its moduli map is integral and it preserves closed points". Eight results,
  all scheme finiteness/quasi-finiteness lemmas; no adequate-stack statement.
- `msearch.py ... leansearch`: "finite morphism of algebraic stacks with adequate
  moduli spaces integral induced map". Eight scheme finite/integral results;
  no stack comparison theorem.
- `msearch.py ... loogle`: `"AlgebraicGeometry", "IsFinite"`. Twelve scheme
  results, including `IsFinite.iff_isIntegralHom_and_locallyOfFiniteType`;
  no adequate-stack assertion.
- `msearch.py ... grep`: `AdequateModuli|adequateModuli|adequate_moduli` in
  Mathlib/AlgebraicGeometry: zero hits.
- `rg` of `lean/WeilConjectures` for the item id and adequate/finiteness
  combinations: no corresponding theorem. `rg` of `lean/Sheaf` found
  `AdequateModuliSpace.lean` and consumers, with no comparison theorem.
- `rg` of both source roots and `dag/lean_names_upstream.json` for
  `adequate_integral_comparison_finite|AdequateIntegralComparisonFinite`:
  no existing declaration before writing.
- Searches for smooth finite-type atlases, scheme/space tests, stack diagonals,
  structural maps and point topology found the reused interfaces listed above;
  no private redefinitions were needed.

Validation: the repaired module compiled through scompile.py against the published
live library in both sandbox and library contexts (9.9 s and 10.9 s), with no
errors or warnings. The repaired signature is copied verbatim into lean.statement.
The delivery dry run checks this packet again before redelivery.

## Second reading by Q94

This dispatcher assignment authorizes self-delivery and assigns independent
review to the maintainer; it explicitly forbids starting another agent.
Accordingly this paragraph records the worker's own rereading, not a claim of
an independent worker review. Reopened the node and the finished module and
matched the hypotheses and conclusion as above. The substantive interface
checks were that `HasSmoothFiniteTypeModuliAtlas` is too specialized for this
node, that `ModuliPointIsClosed` uses DM étale atlases, and that Mathlib's
`LocallyQuasiFinite` does not itself require local finite type. The delivered
signature instead uses smooth finite-type atlases, smooth point topology and
the explicit conjunction of local finite type with local quasi-finiteness.
No change to the node's mathematical statement was necessary.


## Repair of returned head 66aecc7a43f2

H4 and theorem statement dependency: the returned version used
`moduliSmoothPointTopology`, a generateFrom definition in the theorem module
`SmoothPresentationClosedSubsets`. That duplicated the topology notion already
owned by the landed definition node `def-sfb-stack-point-topological-space`.
Read that node and the full signature, construction and docstring of its
recorded `CategoryTheory.moduliPointTopologicalSpace` instance in
`StackPointTopologyFlatLfpOpen`. It constructs the supremum of the coinduced
topologies from all smooth surjective scheme atlases, with the existing
residue-field point maps, exactly the topology needed here.

The repair replaces `lem-sfb-smooth-presentation-closed-subsets` in stmt_deps
by `def-sfb-stack-point-topological-space`, and publicly imports
`StackPointTopologyFlatLfpOpen`. The closed-point hypothesis now reads
`IsClosed ({x} : Set (ModuliPoints U)) →
IsClosed ({moduliPointMap f x} : Set (ModuliPoints V))`, using that instance.
The smooth-presentation theorem remains in proof_deps and its module is retained
as a plain proof import under the stage-2 proof-import rule. There is no use of
`moduliSmoothPointTopology` in the repaired module or recorded signature.
The signature is recopied verbatim into lean.statement.

Compared the retained sandbox packet with current main: main still has no Lean
record and its original six stmt_deps; the sandbox retains the returned
statement and its six added interface dependencies. Current main differs only
in lean and stmt_deps, so the delivery wrapper can rebase the repaired packet
without overwriting any other field. The mathematical statement, proof,
proof_deps and all other checked clauses are unchanged. No new node or
dependency module is introduced.
