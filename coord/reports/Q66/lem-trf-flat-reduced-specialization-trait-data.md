## Worker report

The module `Sheaf.AlgebraicGeometry.FlatReducedSpecializationTraitData` states
`AlgebraicGeometry.exists_flat_reduced_specialization_trait_data`, with its sole
proof `sorry`. It defines no new notion. The source is Stacks Project,
`more-morphisms.tex`, Tag 055Q, second proof paragraph; I read the local source,
the current blueprint ancestor `lem-trf-local-term-locality` and its proof, and
the current chapter and unit. The accepted node statement and split are unchanged.
No new nodes, dependency repairs, statement corrections, or disputed statements
are needed.

For the following clause mapping, write S = `Spec (.of R)`, b = `a ≫ g`,
X = `pullback g (a ≫ g)`, f = `pullback.snd g (a ≫ g)`,
r = `pullback.fst g (a ≫ g)`, eta = `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)`,
and s = `closedPoint R`. These are explanatory abbreviations only, not local
notation or hidden `let` binders in the Lean statement.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| P and T are schemes | `{P T : Scheme.{u}}` |
| P and T are Noetherian: locally Noetherian and quasi-compact | `[IsNoetherian P] [IsNoetherian T]`; Mathlib's class extends `IsLocallyNoetherian` and `CompactSpace` |
| g is a morphism | `(g : P ⟶ T)` |
| g is flat | `[Flat g]` |
| g is of finite presentation | `[LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]`, precisely the three required conditions |
| sigma is a section | `(σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T)` |
| p and q are points, p specializes to q, p differs from q | `{p q : P} (hpq : p ⤳ q) (hne : p ≠ q)` |
| C(g,sigma) and q's membership | `(hq : q ∈ connectedComponentIn (g ⁻¹' {g q}) (σ (g q)))` |
| reduced geometric fibre over g(q) | `hred : IsReduced (pullback g (... ≫ T.fromSpecResidueField (g q)))`, where `...` is `Spec.map` of `algebraMap (T.residueField (g q)) (AlgebraicClosure (T.residueField (g q)))` |
| existence of an integral DVR | `∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)`; the last class includes locality, principal ideals, and non-fieldness |
| a : S to P takes eta to p and s to q | existential `a : Spec (.of R) ⟶ P` followed by `a eta = p ∧ a s = q` |
| b, X, f, r are the prescribed composite and fibre product/projections | the expressions `a ≫ g`, `pullback g (a ≫ g)`, `pullback.snd g (a ≫ g)`, `pullback.fst g (a ≫ g)` throughout |
| f is flat and of finite presentation | four conjuncts `Flat f`, `LocallyOfFinitePresentation f`, `QuasiCompact f`, `QuasiSeparated f` |
| S and X are Noetherian | `IsNoetherian (Spec (.of R)) ∧ IsNoetherian (pullback g (a ≫ g))` |
| closed fibre X_s is Noetherian | `IsNoetherian (f.fiber s)` |
| its topological space is Noetherian, descending closed chains stabilize | `TopologicalSpace.NoetherianSpace (f.fiber s)`: `noetherianSpace_TFAE` identifies this with well-founded strict inclusion on closed subsets, which gives exactly the stated chain stabilization |
| geometric closed fibre is reduced | `IsReduced (pullback f (... ≫ S.fromSpecResidueField s))` using the algebraic closure of `S.residueField s` |
| ordinary closed fibre is reduced | `IsReduced (f.fiber s)` |
| sigma_R and tau are maps S to X | `∃ (σR τ : Spec (.of R) ⟶ pullback g (a ≫ g))` |
| both are sections of f | `σR ≫ f = 𝟙 S ∧ τ ≫ f = 𝟙 S` |
| r composed with sigma_R equals sigma composed with b | `σR ≫ r = (a ≫ g) ≫ σ` |
| r composed with tau equals a | `τ ≫ r = a` |
| sigma_R is the induced section, tau is the graph lift | each map has exactly the two projections specified in the preceding three rows, which uniquely determine it by `pullback.hom_ext`; these are the existing base-changed section and the lift of `(a, 𝟙 S)`, not arbitrary choices |
| r(tau(eta)) = p and r(tau(s)) = q | the two explicit point-image conjuncts using `pullback.fst` and `τ` |
| C(f,sigma_R) equals r-inverse C(g,sigma) | equality of the two displayed sets using `connectedComponentIn` of the actual topological fibres and `r ⁻¹'` on the right |
| tau(s) is in the component of sigma_R(s) in the closed fibre | `τ s ∈ connectedComponentIn (f ⁻¹' {s}) (σR s)` |

Geometric fibres use the canonical algebraic closures, as in the exact
`def-weil-geometric-fibre` record. This fixes the permitted choice; it imposes no
restriction on the residue fields or on their characteristic. Isomorphism
independence is part of that existing definition node. The set C is written
inline with the same Mathlib expression used by the recorded cartesian
section-component theorem; it is not defined a second time.

Statement dependency declarations read and used:

- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat`; the recorded `iff_flat_stalkMap` equates this with
  the node's local-ring definition.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-weil-pbc-scheme-conventions`: a convention record without a declaration;
  use `AlgebraicGeometry.QuasiCompact` and `AlgebraicGeometry.QuasiSeparated`
  from `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` and `.QuasiSeparated`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`; its `IsNoetherian` class includes
  precisely this and topological quasi-compactness.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom`.
- `def-pc-section`: `Mathlib.CategoryTheory.EpiMono`,
  `CategoryTheory.SplitEpi`; use its equivalent unbundled form, a morphism
  together with its section equation, as explicitly permitted by mathlib_match.
- `def-weil-connected-scheme`: `Mathlib.Topology.Connected.Basic`,
  `ConnectedSpace`, and its existing component notion `connectedComponentIn`.
- `def-weil-geometric-fibre` and `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`.
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` supplies `AlgebraicClosure`.
- `def-pc-reduced-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsReduced`, with the read stalkwise equivalence.
- `def-sc-discrete-valuation-ring`:
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, `IsDiscreteValuationRing`.
- `def-pc-base-change`:
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`, specifically the
  canonical pullback/projection convention and
  `AlgebraicGeometry.baseChange_section_characterization`; the recorded module
  and the underlying `sectionBaseChange` declaration in
  `WeilConjectures.AlgebraicGeometry.Picard.Defs` were read in full.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `AlgebraicGeometry.Scheme.Hom.fiber`, `.fiberι`, `.fiberToSpecResidueField`,
  `.fiberHomeo`. This arrives publicly through BaseChangeConventions.

All stated proof dependencies are also imported. Additional plain imports are
`WeilConjectures.AlgebraicGeometry.NoetherianSpecializationTrait`
(`AlgebraicGeometry.exists_trait_of_strict_specializes`),
`WeilConjectures.AlgebraicGeometry.SectionComponentPullback`
(`AlgebraicGeometry.section_component_preimage_of_isPullback`),
`Sheaf.TraceFormula.GeometricReducedFibreLocusBaseChange`
(`AlgebraicGeometry.geometricReduced_fibre_locus_baseChange`),
`Sheaf.AlgebraicGeometry.GeometricallyReducedAlgebraicClosureTest`
(`AlgebraicGeometry.geometricallyReduced_iff_isReduced_pullback_algebraicClosure`),
and `Mathlib.AlgebraicGeometry.Geometrically.Integral` (the geometric reducedness
notion also supplied by `def-pc-geometrically-irreducible`). The remaining proof
leaves are in the public Mathlib imports: flat and finite-presentation base
change, qcqs permanence, affine qcqs, the local finite-type pointwise criterion,
finite-type-over-Noetherian, and Noetherian closed-subset minimality. The
nine-step theorem docstring records every step and its DAG dependencies.

Edge cases checked before writing: empty P or T is excluded already by the
hypotheses (p and q exist, and g has a section); no nonemptiness hypothesis was
added. The strictness is only p != q: g(p) = g(q), including constant b, is
allowed. No separation or finite-type assumption on a or b is imposed. The
closed residue field may be imperfect and of either characteristic. The two
sections may coincide. The DVR is not allowed to be a field, exactly as in the
node. Points eta and s are the zero prime and the unique maximal prime,
respectively. Universes follow the upstream trait theorem: P, T, and R use u,
so all residue fields and their algebraic closures fit in the same scheme
universe; no independent smaller test universe or size equality is introduced.
All variables and universes are explicitly bound, with both implicit-variable
options disabled. No local notation, local instance, or hidden definition is
used.

Searches made (recorded also in sandbox searches.jsonl by msearch.py):

- LeanFinder: “Realize a strict specialization in a Noetherian scheme by a DVR
  and base change a flat finitely presented family with two sections and reduced
  closed fibre”. Eight hits, for valuative-criterion specializing maps, the
  specialization order, flat generalizing maps and stalk specialization. None
  states the combined trait/fibre/two-section result.
- LeanSearch: “A flat finitely presented family over a Noetherian base pulled
  back to a DVR tracing a strict specialization has two sections and reduced
  closed fibre”. Eight hits, for smooth implies lfp, flatness, localized flat
  modules and flat morphisms being universally open; no exact statement.
- Loogle: `AlgebraicGeometry.Flat, IsDiscreteValuationRing`: zero hits.
- msearch grep: `specializ.*[dD][vV][rR]|[dD][vV][rR].*specializ|trait.*section`:
  zero hits.
- Project rg: specialization/trait and `sectionBaseChange|geometricFiberAt`
  in the named source/project trees located the exact existing trait theorem,
  canonical section construction, and the smooth special-case consumers.
  No declaration combines all clauses of this flat/reduced result.
- `grep -rn 'lem-trf-flat-reduced-specialization-trait-data'
  lean/WeilConjectures`, and rg of this id in `lean/Sheaf` and
  `dag/lean_names_upstream.json`: no existing declaration for this node.
- Additional rg for `trait.*[Dd]ata|flat_reduced.*trait|flatReduced.*Trait`
  in both project trees: no matching declaration.

Validation: scompile.py compiled the delivered module in sandbox and library
modes, cleanly, each within three seconds. The first check caught a missing
namespace opening for NoetherianSpace and a carrier inference issue in the set
binder; opening TopologicalSpace and explicitly writing the carrier
`↥(pullback g (a ≫ g))` resolved them without changing the statement.
The maximum Lean line width is 87. The node's only changed field is lean.

## Second reading by Q66

Final self-check of the node and module, not a claim of an independent agent
review: the dispatcher explicitly prohibits starting other agents; the
maintainer performs the independent review after delivery. I reread every
hypothesis and conclusion against the clause table above. In particular,
IsNoetherian on both input schemes includes exactly the two stated properties;
finite presentation includes all three conditions on both g and f; the two
closed-fibre reducedness assertions concern different schemes; and the final
component membership is in f-inverse {s}, not an ambient connected component.
The existential sections are uniquely constrained by both projections, so no
canonical construction is replaced by unconstrained data. All four images of
the generic/closed point, both section equations, and the locus equality are
present with the correct composition order. No further mismatch was found.
